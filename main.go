package main

import (
	"bufio"
	"encoding/base64"
	"encoding/gob"
	"flag"
	"fmt"
	"log"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"time"
)

// Represents an observed change.  nil means no change; otherwise, a string
// describing the change.
type Change *string

// Returns a Change described by fmt.Sprintf(format, args...)
func Changef(format string, args ...interface{}) Change {
	ch := fmt.Sprintf(format, args...)
	return &ch
}

// A check to see if something has changed.
type Check interface {
	Changed() Change
}

// A check composed of multiple other checks.
type CheckMulti []Check

func (c CheckMulti) Changed() Change {
	for _, check := range c {
		if change := check.Changed(); change != nil {
			return change
		}
	}

	return nil
}

// Check to see if the stat() has changed.
// TODO: I guess lstat should be distinguished.
type CheckStat struct {
	Path    string
	Mode    os.FileMode
	ModTime time.Time
}

func (c *CheckStat) Changed() Change {
	stat, err := os.Stat(c.Path)
	if err != nil {
		return Changef("%q no longer exists", c.Path)
	}

	if stat.Mode() != c.Mode {
		return Changef("%q: Mode changed from %s to %s", c.Path, c.Mode, stat.Mode())
	}

	if stat.ModTime() != c.ModTime {
		return Changef("%q: Mod time changed from %s to %s", c.Path, c.ModTime, stat.ModTime())
	}

	return nil
}

// Checks if the file still doesn't exist.
type CheckNotFound struct {
	Path string
}

func (c *CheckNotFound) Changed() Change {
	_, err := os.Stat(c.Path)
	if os.IsNotExist(err) {
		return nil
	} else {
		return Changef("%q now exists", c.Path)
	}
}

// Checks if the file is a dir.
type CheckDir struct {
	Path string
}

func (c *CheckDir) Changed() Change {
	stat, err := os.Stat(c.Path)
	if err != nil {
		return Changef("%q: stat failed %s", err)
	} else if !stat.IsDir() {
		return Changef("%q: no longer a dir")
	} else {
		return nil
	}
}

var reCall *regexp.Regexp = regexp.MustCompile(`^\d+\s+(\w+)\("(.*?)"(.*)$`)
var reIgnore *regexp.Regexp = regexp.MustCompile(`^\d+\s+(\+{3}|-{3})`)

// Parse a line from strace into a Check.
func ParseLine(line string) (Check, error) {
	if reIgnore.MatchString(line) {
		return nil, nil
	}

	var m []string

	if m = reCall.FindStringSubmatch(line); m == nil {
		return nil, fmt.Errorf("Couldn't parse %q", line)
	} else {
		//call := m[1]
		path := m[2]

		if strings.HasPrefix(path, "/tmp") || strings.HasPrefix(path, "/proc") {
			return nil, nil
		}

		//args := m[3]
		abs, err := filepath.Abs(path)
		if err != nil {
			return nil, err
		}

		stat, err := os.Stat(abs)
		if os.IsNotExist(err) {
			return &CheckNotFound{abs}, nil
		} else if err != nil {
			return nil, err
		} else if stat.IsDir() {
			return &CheckDir{
				Path: abs,
			}, nil
		} else {
			return &CheckStat{
				Path:    abs,
				Mode:    stat.Mode(),
				ModTime: stat.ModTime(),
			}, nil
		}
	}
}

// Run a command, strace it, and return a Check that can be used to see if the
// program's dependent state has changed.
func Run(name string, args ...string) (Check, error) {
	r, w, err := os.Pipe()
	if err != nil {
		return nil, err
	}
	defer r.Close()
	defer w.Close()

	strace := []string{"-f", "-o", "/dev/fd/3", "-e", "trace=file", "--"}
	strace = append(strace, name)
	strace = append(strace, args...)
	cmd := exec.Command("strace", strace...)
	cmd.ExtraFiles = []*os.File{w}
	cmd.Stdout = os.Stdout
	cmd.Stderr = os.Stderr
	cmd.Stdin = os.Stdin

	if err := cmd.Start(); err != nil {
		return nil, err
	}

	lineChan := make(chan string)
	scanErrChan := make(chan error)
	finishedChan := make(chan error)

	go func() {
		finishedChan <- cmd.Wait()
	}()

	go func() {
		scanner := bufio.NewScanner(r)
		for scanner.Scan() {
			lineChan <- scanner.Text()
		}
		if err := scanner.Err(); err != nil {
			scanErrChan <- err
		}
	}()

	lines := make([]string, 0)

loop1:
	for {
		select {
		case line := <-lineChan:
			lines = append(lines, line)
		case err := <-finishedChan:
			if err != nil {
				return nil, err
			} else {
				break loop1
			}
		}
	}

loop2:
	for {
		select {
		case line := <-lineChan:
			lines = append(lines, line)
		default:
			break loop2
		}
	}

	checks := make([]Check, 0, len(lines))

	for _, line := range lines {
		check, err := ParseLine(line)
		if err != nil {
			return nil, err
		}

		if check != nil {
			checks = append(checks, check)
		}
	}

	return CheckMulti(checks), nil
}

const cachedir string = ".memo"

// Checks if the command described by cachedir/name needs to be rerun because
// something in its environment has changed.
func NeedsRerun(name string) (bool, error) {
	logfile, err := os.Open(cachedir + "/" + name)
	if os.IsNotExist(err) {
		return true, nil
	} else if err != nil {
		return false, err
	}
	defer logfile.Close()

	check := &CheckMulti{}

	if err := gob.NewDecoder(logfile).Decode(check); err != nil {
		return false, err
	}

	change := check.Changed()

	if change != nil {
		fmt.Println(*change)
	}

	return change != nil, nil
}

func main() {
	flag.Parse()

	gob.Register(CheckMulti{})
	gob.Register(new(CheckStat))
	gob.Register(new(CheckNotFound))
	gob.Register(new(CheckDir))

	if err := os.MkdirAll(cachedir, 0755); err != nil {
		log.Fatalf("Making %q: %s", cachedir, err)
	}

	command := flag.Args()

	name := base64.RawURLEncoding.EncodeToString([]byte(fmt.Sprintf("%v", command)))

	needsRerun, err := NeedsRerun(name)
	if err != nil {
		log.Fatal("Checking if needs rerun", err)
	}

	if needsRerun {
		fmt.Println("Running", command)
		check, err := Run(command[0], command[1:]...)
		if err != nil {
			log.Fatal("Running command", err)
		}

		file, err := os.Create(cachedir + "/" + name)
		if err != nil {
			log.Fatal("Creating tracefile", err)
		}
		defer file.Close()

		if err := gob.NewEncoder(file).Encode(check); err != nil {
			log.Fatal("Decoding tracefile", err)
		}
	} else {
		fmt.Println("Skipping", command)
	}
}
