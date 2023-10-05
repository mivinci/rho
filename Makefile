CC = gcc
AR = ar
CFLAGS = -Wall


all: librho.a


librho.a: rho.o
	$(AR) rcs $@ $^


%.o: %.c
	$(CC) $(CFLAGS) -c -o $@ $<


.PHONY: install
install: librho.a rho.h
	cp librho.a /usr/local/lib/
	cp rho.h    /use/local/include/


.PHONY: clean
clean:
	rm *.o
	rm *.a