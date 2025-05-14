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

# Default Target
all: $(LIBRARY)

# Ensure build directory exists
build/:
	mkdir -p build

# Build the shared library
$(LIBRARY): $(OBJ) | build/
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
