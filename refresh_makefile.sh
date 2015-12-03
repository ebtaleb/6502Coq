#/bin/bash

{ echo '-R . 6502Coq' ; find -name '*.v' -print; } > _CoqProject && coq_makefile -f _CoqProject -o Makefile
