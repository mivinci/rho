CC     := gcc
AR     := ar
CFLAGS := -Wall

ifeq ($(OPT), 1)
	CFLAGS += -O2
endif

ifeq ($(DEBUG), 1)
	CFLAGS += -g -DRHO_DEBUG
endif


all: librho.a


librho.a: rho.o
	$(AR) rcs $@ $^


%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<


.PHONY: clean
clean:
	rm *.out
	rm *.o
	rm *.a


test_parse.out: test_parse.c rho.h librho.a
	$(CC) $(CFLAGS) -o $@ test_parse.c -L. -lrho

test_load.out: test_load.c rho.h librho.a
	$(CC) $(CFLAGS) -o $@ test_load.c -L. -lrho

test_append.out: test_append.c rho.h librho.a
	$(CC) $(CFLAGS) -o $@ test_append.c -L. -lrho
