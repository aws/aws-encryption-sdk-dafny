using System.Collections.Generic;
using System.Linq;
using KeyringDefs;
using KMSKeyringDefs;
using KMSUtils;
using STL;
using charseq = Dafny.Sequence<char>;

namespace AWSEncryptionSDK
{
    public class Keyrings
    {
        public static Keyring MakeKMSKeyring(ClientSupplier clientSupplier,
                                             IEnumerable<string> keyIDs,
                                             string generator,
                                             IEnumerable<string> grantTokens)
        {
            KMSKeyring result = new KMSKeyring();
            result.__ctor(
                clientSupplier, 
                Dafny.Sequence<charseq>.FromElements(keyIDs.Select(DafnyFFI.DafnyStringFromString).ToArray()),
                DafnyFFI.NullableToOption(generator != null ? DafnyFFI.DafnyStringFromString(generator) : null),
                Dafny.Sequence<charseq>.FromElements(grantTokens.Select(DafnyFFI.DafnyStringFromString).ToArray()));
            return result;
        }
    }
}