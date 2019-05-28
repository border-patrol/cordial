# ----------------------------------------------------------------- [ Makefile ]
# Module    : Makefile
# Copyright : (c) Jan de Muijnck-Hughes
# License   : see LICENSE
# ---------------------------------------------------------------------- [ EOH ]

IDRIS := idris
LIB   := cordial
ETC   := examples
OPTS  :=

.PHONY: doc cthulhu check clean build install examples

usuage:
	@echo "Targets are:"
	@echo ""
	@echo "Build Targets"
	@echo "\t make check   -- type check only"
	@echo "\t make build   -- build package"
	@echo "\t make install -- install library"
	@echo ""
	@echo "Clean Targets"
	@echo "\t make clean   -- build idris doc"
	@echo "\t make cthulhu -- build idris doc"
	@echo ""
	@echo "Testing & Examples"
	@echo "\t make examples -- build examples"
	@echo ""
	@echo "Documentation"
	@echo "\t make doc       -- build idris doc"
	@echo "\t make highlight -- generate highlight files for idrishl"

install: build
	${IDRIS} ${OPTS} --install ${LIB}.ipkg

build:
	${IDRIS} ${OPTS} --build ${LIB}.ipkg

examples:
	${IDRIS} ${OPTS} --build ${ETC}.ipkg

highlight: cthulhu
	${IDRIS} ${OPTS} --checkpkg ${LIB}.ipkg --highlight
	${IDRIS} ${OPTS} --checkpkg ${ETC}.ipkg --highlight


clean:
	${IDRIS} --clean ${LIB}.ipkg
	${IDRIS} --clean ${ETC}.ipkg
	find . -name "*~" -delete


cthulhu: clean
	find src   \( -name "*.idh"   \
		 -or -name "*.html" \
		 -or -name "*.tex"  \
		 -or -name "*.ibc"  \
		 \)                 \
		 -delete

doc:
	${IDRIS} --mkdoc ${LIB}.ipkg
	${IDRIS} --mkdoc ${ETC}.ipkg
# ---------------------------------------------------------------------- [ EOF ]
