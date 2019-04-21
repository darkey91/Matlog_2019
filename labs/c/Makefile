.PHONY: all, run, clean
SOURCES=$(shell find -type f -name "*.cpp")
HEADERS=$(shell find -type f -name "*.h")

all: $(SOURCES)
	g++ $(HEADERS) $(SOURCES) --std=c++14 -o program
run:
	./program
clean:
	rm ./program

