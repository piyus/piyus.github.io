#include <stdio.h>

// Compile using:: gcc -fno-stack-protector -O1 CallConv.c
// Disassemble using: objdump -dx a.out > disasm.txt
// Inspect disasm.txt to identify the gcc calling convention

struct Node16 {
	size_t a, b;
};

struct Node24 {
	size_t a, b, c;
};


int __attribute__((noinline)) f1(int a, int b, int c, int d, int e, int f, int g, int h)
{
	return a + b + c + d + e + f + g + h;
}

struct Node24 __attribute__((noinline)) f2(int a, int b, int c)
{
	struct Node24 t = {a, b, c};
	return t;
}

struct Node16 __attribute__((noinline)) f3(int a, int b)
{
	struct Node16 t = {a, b};
	return t;
}

size_t __attribute__((noinline)) f4(struct Node24 a, struct Node16 b)
{
	return a.a + a.b + a.c + b.a + b.b;
}

int main()
{
	int Ret = f1(1, 2, 3, 4, 5, 6, 7, 8);
	struct Node24 t1 = f2(Ret, 2, 3);
	struct Node16 t2 = f3(1, 2);
	size_t RetVal = f4(t1, t2);
	return (int)RetVal;
}
