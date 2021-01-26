//@ ensures \result.length() == s.length();
String[] reverse(String [] s) { ... }

//@ requires amount > 0;
//@ ensures balance > \old(balance);
void deposit(int amount) {
    this.balance += amount;
}
