CC     := gcc
AR     := ar
CFLAGS := -Wall -O2

ifeq (DEBUG, 1)
	CFLAGS += -g -DDEBUG
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
