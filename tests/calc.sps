#!r6rs
(import (rnrs io simple)
        (logji base)
        (logji zbepi load))
(write (load "/home/d/zone/logji/tests/calc.scm" base-env))
(newline)
