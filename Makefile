COQMK = CoqSrc.mk

FORCE:

coq: coq/*.v coq/_CoqProject
	cd coq; make -f $(COQMK)

impl: FORCE
	cd impl; stack build

clean:
	cd coq; rm -f *.vo *.vok *.vos *.glob *.conf .*.aux .lia.cache $(COQMK).conf .$(COQMK).d
	cd agda; rm -f *.agdai
	cd impl; stack clean --full

zip:
	rm -f stratt.zip
	zip stratt -r Makefile README.md StraTT.ott \
		impl/app/ impl/pi/ impl/src/ impl/README.md impl/stack.yaml impl/stratt.cabal \
		coq/_CoqProject coq/CoqSrc.mk coq/README.md coq/*.v agda/*.agda
