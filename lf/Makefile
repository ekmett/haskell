build:
	@cabalc build

install:
	@cabalc install

watch:
	@ghcid

uninstall: 
	@rm -rf ../dist-newstyle/build/x86_64-osx/ghc-8.10.1/lf-0/

over: uninstall build

.PHONY: build install watch uninstall over
