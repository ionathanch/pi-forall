COQMK = CoqSrc.mk

FORCE:

coq: coq/*.v coq/_CoqProject
	cd coq; make -f $(COQMK)

coqmk: coq/_CoqProject
	cd coq; coq_makefile -f _CoqProject -o CoqSrc.mk

coq/StraTT_ott.v: StraTT.ott
	ott -i StraTT.ott -o coq/StraTT_ott.v -coq_lngen true -coq_expand_list_types true

coq/StraTT_inf.v: StraTT.ott
	lngen --coq coq/StraTT_inf.v --coq-ott StraTT_ott StraTT.ott

impl: FORCE
	cd impl; stack build

clean:
	cd coq; rm -f *.vo *.vok *.vos *.glob *.conf .*.aux .lia.cache $(COQMK).conf .$(COQMK).d
	cd agda; rm -f *.agdai
	cd impl; stack purge

zip:
	rm -f stratt.zip
	zip stratt -r Makefile README.md LICENSE StraTT.ott start.sh disk.qcow2 \
		impl/app/ impl/pi/ impl/src/ impl/README.md impl/stack.yaml impl/stratt.cabal \
		coq/_CoqProject coq/CoqSrc.mk coq/README.md coq/*.v agda/*.agda \
		-x agda/model.agda
