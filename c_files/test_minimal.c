#include <stdlib.h>
#include <stdio.h>

int main(void)
{
    leak(10);
}

int leak(int x)
{

    int *p = malloc(sizeof(int));

    if (x > 0)
    {
        free(p);
    }

    return 0;
}