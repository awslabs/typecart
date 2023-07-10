This is the same example as the signed_int example with the exception that

* we use constraints in specifying the datatypes
* when forward/backward translating, we translate across data constructors.  
  specifically we translate POS(0) <==> ZERO

  Under this translation, forward and backward compatibility both hold.  
