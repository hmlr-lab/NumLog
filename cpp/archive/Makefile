# Compiler and Linker
CXX = clang++
CXXFLAGS = --std=c++17
CXXFLAGS += $(shell pkg-config swipl --cflags)

LD = clang++  # Linker for the final executable
LDFLAGS = -std=c++17 $(shell pkg-config --libs swipl)


CXXFLAGS += -I/opt/homebrew/include/

# Source and Object Files
SRC = $(wildcard src/*.cpp)
OBJ = $(SRC:.cpp=.o)
EXEC = build/numlog  # Executable target
LIBRARY = build/numlog.so  # Remove this if you're not using the shared library

# Default Target
all: $(EXEC)

# Ensure build directory exists
build/:
	mkdir -p build

# Link the Executable (no -shared flag, just linking object files)
$(EXEC): $(OBJ)
	$(LD) $(OBJ) -o $@ $(LDFLAGS)
	mkdir -p $(DESTDIR)
	mv $@ $(DESTDIR)

# Compile .cpp files to .o
src/%.o: src/%.cpp | build/
	$(CXX) $(CXXFLAGS) -c -o $@ $<

# Cleaning Rules
.PHONY: clean mrproper all

clean:
	rm -rf build/*.o build/$(EXEC)

mrproper: clean
	rm -f build/$(EXEC)
