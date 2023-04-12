/*
@rho

x = 100
y = 3.14
z = "hello"

print x + y
print z


@rho_assembly


.fun main 3
.int 100
.flt 3.14
.str "hello"

pushc  0 (100)
popv   0 (x)
pushc  1 (3.14)
popv   1 (y)
pushc  2 ("hello")
popv   2 (z)
pushv  0 (x)
pushv  1 (y)
add
print
pushv  2 (z)
print
ret
*/
