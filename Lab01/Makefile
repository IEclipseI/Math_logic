SOURCES=src/Main.hs src/Grammar.hs
GEN_SOURCES=src/Lexer.x src/Parser.y
GENERATED=src/Lexer.hs src/Parser.hs
PACKAGE=hw1.zip

.PHONY: pack all run clean

all: parser

run: 
	./parser

clean:
	rm -rf src/*.o src/*.hi
	rm -f parser
	rm -f hw1.zip

parser: $(GENERATED) $(SOURCES)
	ghc -i./src -tmpdir . ./src/Main.hs -o parser

pack: $(GENERATED)
	zip $(PACKAGE) -r Makefile src/*.hs