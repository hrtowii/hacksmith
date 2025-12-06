#include <stdio.h>
#include <stdbool.h>

bool isLeapYear(int year) {
    return ((year % 4 == 0 && year % 100 != 0) ||
            (year % 400 == 0));
}

int main(void) {
    int year = 1980;
    int days;

    printf("Enter days value: ");
    scanf("%d", &days);

    while (days > 365) {
        if (isLeapYear(year)) {
            if (days > 366) {
                days -= 366;
                year += 1;
            }
        } else {
            days -= 365;
            year += 1;
        }
    }

    printf("Final year: %d\n", year);
    printf("Remaining days: %d\n", days);

    return 0;
}