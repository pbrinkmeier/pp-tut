.source HelloWorld.java
.class public HelloWorld
.super java/lang/Object

.method public static main([Ljava/lang/String;)V
  .limit stack 2

  ; Legt System.out auf den Stack
  getstatic java/lang/System/out Ljava/io/PrintStream;
  ; Legt "Hello, Jasmin!" auf den Stack
  ldc "Hello, Jasmin!"
  ; Ruft PrintStream.println auf:
  ; this     = System.out
  ; argument = "Hello, Jasmin!"
  invokevirtual java/io/PrintStream/println(Ljava/lang/String;)V
  return
.end method
