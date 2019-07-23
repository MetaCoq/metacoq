(module foo
 (main main)
 (import (erase "erase.scm")))

(define (main argv)
  (print "argv: " argv)
  (print (erase_prog)))
