class BankAccount {
    private int balance = 0;

    public void deposit(int amount) {
        if (amount > 0) {
            balance += amount;
        }
    }

    public void withdraw(int amount) {
        if (amount <= balance) {
            balance -= amount;
        }
    }

    public int getBalance() {
        return balance;
    }
}
