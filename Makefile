SOURCES=TypeCheck.hs PrettyPrint.hs LayoutToken.hs Parser.hs Syntax.hs Environment.hs Modules.hs Arbitrary.hs Equal.hs
TEST=Makefile Lec1.pi Lec2.pi Lec3.pi Hw1.pi Hw2.pi NatChurch.pi Logic.pi Equality.pi Product.pi Nat.pi Fin.pi FinHw.pi Vec.pi BoolLib.pi List.pi Lambda.pi Lambda0.pi Lambda1.pi Lambda2.pi BoolLib.pi Lec4.pi Product1.pi Fix.pi Lennart.pi Hurkens.pi Equal.pi
SRCS=$(addprefix src/,$(SOURCES)) app/Main.hs test/Main.hs

EXTRA=LICENSE README.md pi-forall.cabal stack.yaml

SOLNS=$(addprefix ../src/,$(SRCS)) $(addprefix ../src/pi/, $(TEST))

STUBREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN.*?STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg'
SOLNREGEX='BEGIN { undef $$/; } s/[\{][-]\s*?SOLN\s*?[-][\}](\s*\r?\n|\s)(.*?)[\{][-]\s*STUBWITH(\s*\r?\n|\s)(.*?)\s*[-][\}]/$$2/sg'

FORMAT=ormolu --ghc-opt -XImportQualifiedPost --mode inplace

flags=

all: full

test : all test_full

# BUILD = cabal new-build --disable-documentation
# EXEC = cabal new-exec pi-forall --

BUILD = stack build
EXEC = stack exec pi-forall --

full: $(SOLNS) Makefile $(EXTRA)
	cd ../src && $(BUILD)

test_full: ../src
	cd ../src/pi && make
	stack test

uninstall:
	-ghc-pkg unregister `ghc-pkg list | grep pi-forall`
	@echo
	@echo You need to manually delete any pi-forall binaries on your path.
	@echo You can find them with \`which pi-forall\`

clean:
	-rm -rf dist/ dist-newstyle/ .stack-work/

test:
	cd pi && make

# adds a link to the executable in the test directory
pi: cabal-dev
	cabal-dev install --disable-documentation .
	ln -fs `pwd`/cabal-dev/bin/pi-forall pi

# You need to have the cabal install dir on your path (by default
# ~/.cabal/bin) so that `cabal-dev` command is found.
cabal-dev:
	cabal install --overwrite-policy=always cabal-dev

../full/% : % Makefile $(EXTRA)
#	-chmod 640 $@ 2> /dev/null
	cp $< $@
	@perl -i -pe $(subst SOLN,SOLN HW,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN DATA,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EQUAL,$(SOLNREGEX)) $@
	@perl -i -pe $(subst SOLN,SOLN EP,$(SOLNREGEX)) $@
#	chmod 440 $@ # prevent inadvertent modification of stub code
