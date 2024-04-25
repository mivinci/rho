CC     := gcc
AR     := ar
CFLAGS := -Wall

ifeq ($(OPT), 1)
	CFLAGS += -O2
endif

ifeq ($(DEBUG), 1)
	CFLAGS += -g -DRHO_DEBUG
endif


all: rho


rho: main.c rho.h librho.a
	$(CC) $(CFLAGS) -o $@ main.c -L. -lrho


librho.a: rho.o
	$(AR) rcs $@ $^


%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<


.PHONY: clean
clean:
	rm *.o
	rm *.a
	rm *.out

test_append.out: test_append.c rho.h librho.a
	$(CC) $(CFLAGS) -o $@ test_append.c -L. -lrho
