package bruteforce;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.List;
import java.util.function.Supplier;
import javax.xml.bind.DatatypeConverter;

public class Bruteforce {
    public static void main(String[] args) {
        int wordlen = 5;
        int k = 2;
        Bruteforce b = new Bruteforce(wordlen);

        long count1 = Bruteforce.time("Sequential", () -> {
            return b.countZeroStartSequential(k);
        });
        System.out.println(String.format("Sequential found %d hashes starting with %d zeroes.", count1, k));

        long count2 = Bruteforce.time("Parallel", () -> {
            return b.countZeroStartParallel(k, Runtime.getRuntime().availableProcessors());
        });
        System.out.println(String.format("Parallel found %d hashes starting with %d zeroes.", count2, k));
    }

    //////
    
    private final int wordlen;
    
    public Bruteforce(int wordlen) {
        this.wordlen = wordlen;
    }

    public long countZeroStartSequential(int prefixlen) {
        MessageDigest d = Bruteforce.sha256digest();
        long wordCount = (long) Math.pow(26, this.wordlen);
        long result = 0;
        byte[] word = Bruteforce.numToWord(this.wordlen, 0);

        for (long i = 0; i < wordCount; i++) {
            byte[] currentHash = d.digest(word);

            if (Bruteforce.hasZeroPrefixOf(prefixlen, currentHash)) {
                System.out.println(DatatypeConverter.printHexBinary(currentHash));
                result++;
            }

            Bruteforce.nextWord(word);
        }

        return result;
    }

    public long countZeroStartParallel(int prefixlen, long n) {
        return 0;
    }

    ////// utilities

    public static <T> T time(String title, Supplier<T> f) {
        long start = System.currentTimeMillis();
        T result = f.get();
        long end = System.currentTimeMillis();

        System.out.println(String.format("%s took %dms", title, end - start));
        return result;
    }

    public static boolean hasZeroPrefixOf(int prefixlen, byte[] bytes) {
        for (int i = 0; i < prefixlen && i < bytes.length; i++) {
            if (bytes[i] != 0) {
                return false;
            }
        }

        return true;
    }

    public static byte[] numToWord(int len, long n) {
        byte[] word = new byte[len];

        for (int i = len - 1; i >= 0 && n >= 0; i--) {
            word[i] = (byte) ('a' + (n % 26));
            n /= 26;
        }

        return word;
    }

    public static void nextWord(byte[] c) {
        int i = c.length - 1;

        while (c[i] == 'z') {
            if (i == 0) { return; }
            c[i--] = 'a';
        }
        c[i]++;
    }

    public static MessageDigest sha256digest() {
        try {
            return MessageDigest.getInstance("SHA-256");
        } catch (NoSuchAlgorithmException e) {
            return null;
        }
    }
}
