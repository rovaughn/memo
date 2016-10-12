package main

import (
	"bufio"
	"crypto/sha512"
	"encoding/hex"
	"flag"
	"fmt"
	"io"
	"math"
	"os"
	"os/exec"
	pathlib "path"
	"regexp"
	"strconv"
	"strings"
	"time"
)

func AnyPrefix(path string, prefices []string) bool {
	for _, prefix := range prefices {
		if strings.HasPrefix(path, prefix) {
			return true
		}
	}

	return false
}

func In(needle string, haystack []string) bool {
	for _, h := range haystack {
		if needle == h {
			return true
		}
	}

	return false
}

// Remember, it's better to have a false dirty than a false clean.
// Needs to be tested against a lot of different programs, esp complicated
// ones like compilers.
func CheckDirty(logPath string) (bool, error) {
	f, err := os.Open(logPath)
	if os.IsNotExist(err) {
		return true, nil
	} else if err != nil {
		return true, err
	}
	defer f.Close()

	r := bufio.NewReader(f)

	reMain := regexp.MustCompile(`^\d+\s+(\d+\.\d+)\s+(\w+?)\((.*?)\)\s+=\s+(.*?)\n$`)
	rePath := regexp.MustCompile(`^"(.*?)"|\d+<(.*?)>,`)
	reOpen := regexp.MustCompile(`^"(.*?)", ([\w|]+)(, (\d+))?`)
	reExit := regexp.MustCompile(`^\d+\s+\d+\.\d+\s+\+\+\+ exited with (-?\d+) \+\+\+\n$`)
	reRet := regexp.MustCompile(`^(-?\d+)\s*(\w+)?`)
	ignoreSyscalls := []string{"brk", "mmap", "fstat", "close", "read", "mprotect", "arch_prctl", "munmap", "dup2", "set_tid_address", "set_robust_list", "rt_sigaction", "rt_sigprocmask", "getrlimit", "statfs" /*?*/, "geteuid", "fadvise64", "write", "lseek", "exit_group"}
	readSyscalls := []string{"execve", "access", "stat"}
	alwaysSyscalls := []string{"utimensat"}
	ignorePaths := []string{"/proc/"}

	var m []string

	for {
		line, err := r.ReadString('\n')
		if err == io.EOF {
			return false, nil
		}

		if m = reExit.FindStringSubmatch(line); m != nil {
			// TODO: We should use the exit value and stuff, but only if it's
			//       the top level process I guess.  Maybe store the exit code
			//       in a variable and return it at the end.
			continue
		}

		m = reMain.FindStringSubmatch(line)
		if m == nil {
			return true, fmt.Errorf("Could not understand %q", line)
		} else {
			timestamp, err := strconv.ParseFloat(m[1], 64)
			if err != nil {
				return true, err
			}

			t := time.Unix(int64(timestamp), int64((timestamp-math.Trunc(timestamp))*1e9))
			syscall := m[2]
			args := m[3]
			ret := m[4]

			if In(syscall, alwaysSyscalls) {
				return true, nil
			} else if In(syscall, ignoreSyscalls) {
				continue
			} else if syscall == "open" {
				m = reOpen.FindStringSubmatch(args)
				if m == nil {
					return true, fmt.Errorf("Could not understand args in %q", line)
				}
				path := m[1]

				if AnyPrefix(path, ignorePaths) {
					continue
				}

				flagSlice := strings.Split(m[2], "|")
				flags := make(map[string]bool)

				for _, flag := range flagSlice {
					flags[flag] = true
				}

				m = reRet.FindStringSubmatch(ret)
				if m == nil {
					return true, fmt.Errorf("Could not understand return value in %q", line)
				}
				//retcode := m[1]
				retname := m[2]

				if flags["O_RDONLY"] {
					fi, err := os.Stat(path)
					if retname == "ENOENT" {
						if !os.IsNotExist(err) {
							return true, nil
						}
					} else if retname == "" {
						if os.IsNotExist(err) {
							return true, nil
						} else if err != nil {
							return true, err
						}

						if t.Before(fi.ModTime()) {
							return true, nil
						}
					} else {
						return true, fmt.Errorf("Could not understand return value %q", retname)
					}
				} else if flags["O_WRONLY"] && (flags["O_TRUNC"] || flags["O_CREAT"]) {
					if retname == "" {
						fi, err := os.Stat(path)
						if os.IsNotExist(err) || fi != nil && t.Before(fi.ModTime()) {
							return true, nil
						} else if err != nil {
							return true, err
						}
					} else if retname == "ENOENT" {
						_, err := os.Stat(pathlib.Dir(path))

						if !os.IsNotExist(err) {
							return true, nil
						}
					} else {
						return true, fmt.Errorf("Could not understand return value %q", retname)
					}
				} else {
					return true, fmt.Errorf("Could not understand flags in %q", line)
				}
			} else if In(syscall, readSyscalls) {
				m = rePath.FindStringSubmatch(args)
				if m == nil {
					return true, fmt.Errorf("Could not understand args in %q", line)
				}
				path := m[1]

				m = reRet.FindStringSubmatch(ret)
				if m == nil {
					return true, fmt.Errorf("Could not understand return value in %q", line)
				}
				//retcode := m[1]
				retname := m[2]

				fi, err := os.Stat(path)
				if retname == "ENOENT" {
					if !os.IsNotExist(err) {
						return true, nil
					}
				} else if retname == "" {
					if os.IsNotExist(err) {
						return true, nil
					} else if err != nil {
						return true, err
					}

					if t.Before(fi.ModTime()) {
						return true, nil
					}
				}

				continue
			} else {
				return true, fmt.Errorf("Unknown syscall in %q", line)
			}
		}
	}
}

func Main() error {
	flag.Parse()
	command := flag.Args()

	if len(command) < 1 {
		return fmt.Errorf("Please supply a command")
	}

	commandHash := sha512.Sum512([]byte(fmt.Sprintf("%#v", command)))
	commandHex := hex.EncodeToString(commandHash[:])
	commandLog := ".memo/" + commandHex

	if dirty, err := CheckDirty(commandLog); err != nil {
		return err
	} else if dirty {
		fmt.Println("dirty, rerun")
		if err := os.MkdirAll(".memo", 0776); err != nil {
			return err
		}

		straceArgs := make([]string, 0)
		straceArgs = append(straceArgs, "-o", commandLog)
		straceArgs = append(straceArgs, "-f", "-y", "-ttt")
		//straceArgs = append(straceArgs, "-e", "trace=file")
		straceArgs = append(straceArgs, command...)

		cmd := exec.Command("strace", straceArgs...)
		cmd.Stderr = os.Stderr

		if err := cmd.Run(); err != nil {
			return err
		}
	} else {
		fmt.Println("skipping")
	}

	return nil
}

func main() {
	if err := Main(); err != nil {
		fmt.Fprintln(os.Stderr, err)
		os.Exit(1)
	}
}
