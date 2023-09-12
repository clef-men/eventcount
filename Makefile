.PHONY : all
all : build

.PHONY : build
build :
	@ zig build test

.PHONY : clean
clean :
	@ rm -rf zig-cache zig-out *.a *.a.o
