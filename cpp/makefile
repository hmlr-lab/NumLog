# Compiler and Linker
CXX = clang++
CXXFLAGS = --std=c++17
CXXFLAGS += $(shell pkg-config swipl --cflags)
CXXFLAGS += -I/opt/homebrew/include/ -fPIC  -Wall -g

LD = clang++  # Linker for the shared library
LDFLAGS = -std=c++17 $(shell pkg-config --libs swipl) -shared

# Source and Object Files
SRC = $(wildcard src/*.cpp)
OBJ = $(SRC:.cpp=.o)
LIBRARY = build/libnumlog.so  # Shared library target
LIBRARY_V2 = ../Libs/libnumlogV2.so

# Default Target
all: $(LIBRARY) $(LIBRARY_V2)

# Ensure build directory exists
build/:
	mkdir -p build

# Build the shared library
$(LIBRARY): $(OBJ) | build/
	$(LD) $(OBJ) -o $@ $(LDFLAGS)

# Build the foreign library loaded by Libs/numlogV2.pl
$(LIBRARY_V2): $(OBJ) | build/
	$(LD) $(OBJ) -o $@ $(LDFLAGS)

# Compile .cpp files to .o with -fPIC
src/%.o: src/%.cpp | build/
	$(CXX) $(CXXFLAGS) -c -o $@ $<

# Cleaning Rules
.PHONY: clean mrproper all

clean:
	rm -rf build/*.o build/$(LIBRARY)

mrproper: clean
	rm -f build/$(LIBRARY)
