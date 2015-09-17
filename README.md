
NAME
----

memo - memoize a command.

SYNOPSIS
--------

**memo** [-**watch**] [-**stdout** *dest*] [-**stderr** *dest*] [-**stdin** *source*] *command* [*args*]

DESCRIPTION
-----------

**memo** runs the given *command* with *args* until it exits.  It uses strace to
detect which files the command depended upon during its execution, and after the
program finishes, stores the state of those files in a file under the cache
directory `.memo`.

When **memo** is called again with the same command, it will check if a state
file already exists; if none of the files have changed, the command is not run;
otherwise, the command is run again, and the state file is updated with the new
dependencies and state.

The exit status is stored so that if the command failed before, it will fail
again.

Environment variables are also stored as input.

By default, stdout and stderr are cached in the cache directory.  If
you’re redirecting stdout/stderr to files like `memo command >dest`, it’d be
more efficient to use `memo -stdout dest command` so that the intermediate
caching file doesn’t have to be created and copied needlessly every time.  There
is also an **-stderr** option described below.

Stdin is cached as well.  If the command has stdin memoized, any incoming stdin
is compared against the cache to determine if the file needs to be rerun.  Note
that this means the command won’t be run until *all* the stdin is read and EOF
is reached, if stdin was received before.

OPTIONS
-------

**-watch**

After running *command* (if it was necessary), wait until any of the
dependency files change again, and rerun command, ad infinitum.  Can be used to
automatically rerun a build script when necessary.

**-watch-kill**

Like **-watch**, but if any dependencies changes, immediately kills the running
command and starts it over.  This is useful for, e.g., servers.

**-stdout** *dest*

Store all the program’s stdout in *dest*.  If this is not given, it is
instead stored in the cache directory.  This is more efficient than redirecting
stdout into a file with the shell, as an intermediate cache file doesn't need to
be stored and copied.

**-stderr** *dest*

Store all the program’s stderr in *dest*.  If this is not given, it is
instead stored in the cache directory.  This is more efficient than redirecting
stderr into a file with the shell, as an intermediate cache file doesn't need to
be stored and copied.

**-stdin** *source*

Use *source* as the stdin for the command.  This is more efficient than
redirecting stdin from a file with the shell, as an intermediate cache file
doesn't need to be stored and copied.

EXAMPLES
--------

Only recompile C files when necessary.  Automatically determines dependencies
(e.g. `.h` files, `.o` files, even files from `/include`)

```bash
    for file in *.c
    do
        memo gcc -o ${file%.c}.o $file
    done
    memo ld *.o
```

TODO
----

- Tests.
- Warn about un-memo-izable syscalls, like network connections.
- Perhaps a separate memo utility for memoizing HTTP requests, using 403 Not
  Modified and such.
- Be able to check by hash instead of mtime.
- Probably more finely tuned syscall checks.  Like access() calls and stuff.
- The "current state" could be derived directly from the strace log.  It'd be
  faster.
- Memoize on environment variables as well.
- Maybe a custom memo key.

