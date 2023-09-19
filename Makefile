COQMK = CoqSrc.mk

coq/$(COQMK):
	cd coq; coq_makefile -arg '-w -variable-collision,-meta-collision,-require-in-module' -f _CoqProject -o $(COQMK)

impl: impl/src impl/app impl/.stack-work
	cd impl; stack build

clean:
	cd coq; rm -f *.vo *.vok *.vos *.conf $(COQMK)
	cd impl; stack clean --full

zip:
	rm -f stratt.zip
	zip stratt -r Makefile StraTT.ott impl/app/ impl/pi/ impl/src/ impl/README.md impl/stack.yaml impl/stratt.cabal coq/_CoqProject coq/README.md coq/*.v agda/*.agda