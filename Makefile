all: install

install: build
	idris --install numdris.ipkg

build: Numdris/*.idr
	idris --build numdris.ipkg

test: build
	idris --testpkg test.ipkg

clean:
	idris --clean test.ipkg
	rm -f tests/*.ibc
