#include <stdlib.h>

void helper(int x)
{

    if (x > 0)
    {
        x--;
    }
}

void process_with_size(int size)
{
    int *buffer = malloc(sizeof(int) * size);

    if (size > 0)
    {
        if (size > 10)
        {
            if (size > 50)
            {

                helper(size);
                free(buffer);
            }
        }
    }
}

int main(void)
{

    process_with_size(100);

    process_with_size(5);

    return 0;
}
