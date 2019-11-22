package Utils;

import org.bouncycastle.jce.provider.BouncyCastleProvider;

import java.security.Security;

public class BouncyCastleUtils {
    private BouncyCastleUtils() { }

    private static final BouncyCastleProvider PROVIDER =
        new BouncyCastleProvider();

    static {
        Security.addProvider(PROVIDER);
    }

    public static BouncyCastleProvider getProvider() {
        return PROVIDER;
    }
}
