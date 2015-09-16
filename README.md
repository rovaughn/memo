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
- Watch mode.
- Handle caching stdin/stdout/stderr.  Perhaps by adding -stdout -stdin -stderr
  options.  Warn when the program emits stdin/stdout/stderr as those will not be
  saved.  Also these should preferably be atomic.  In fact, there should
  generally be utilities for atomically making files, in case a build step
  fails.
- Warn about un-memo-izable syscalls, like network connections.
- Perhaps a separate memo utility for memoizing HTTP requests, using 403 Not
  Modified and such.
- Be able to check by hash instead of mtime.
- Probably more finely tuned syscall checks.  Like access() calls and stuff.
- The "current state" could be derived directly from the strace log.  It'd be
  faster.
- Memoize on environment variables as well.
- Maybe a custom memo key.

