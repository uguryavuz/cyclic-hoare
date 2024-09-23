COQMAKEFILE := CoqMakefile

all:
	coq_makefile -f _CoqProject -o $(COQMAKEFILE)
	make -f $(COQMAKEFILE)

clean:
	rm -f .*.aux *.glob *.vos *.vo *.vok .*.cache
	make -f $(COQMAKEFILE) clean
	rm -f $(COQMAKEFILE) $(COQMAKEFILE).conf