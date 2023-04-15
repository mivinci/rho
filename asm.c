/*
@rho

x = 100
y = 3.14
z = "hello"

print x + y
print z


@rho_assembly

main: .int 100
      .flt 3.14
      .str "hello"

      pshc  0 (100)
      popv  0 (x)
      pshc  1 (3.14)
      popv  1 (y)
      pshc  2 ("hello")
      popv  2 (z)
      pshv  0 (x)
      pshv  1 (y)
      add
      print
      pshv  2 (z)
      print
      ret
*/
