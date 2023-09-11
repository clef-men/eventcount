.PHONY : all
all : build

.PHONY : build
build :
	@ rm -rf zig-cache zig-out
	@ zig build

.PHONY : clean
clean :
	@ rm -rf zig-cache zig-out *.a *.a.o
