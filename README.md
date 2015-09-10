memo
====

Run a command, if necessary.

    memo command arg1 arg2...

Runs `command arg1 arg2` and strace’s it.  It logs the files that the command
depended upon during its execution and stores the state of those files.  When
you rerun the command, it checks the cached log and determines if the command
actually needs to be run again.

TODO
----

- Tests.
- Handle caching stdin/stdout/stderr.  Perhaps by adding -stdout -stdin -stderr
  options.

