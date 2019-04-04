#!r6rs
(import (rnrs io simple)
        (logji base)
        (logji zbepi load))
(write (load "logji/tests/calc.scm" base-env))
(newline)
