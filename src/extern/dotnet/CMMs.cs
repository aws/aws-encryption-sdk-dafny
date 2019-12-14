using CMMDefs;
using ESDK;
using KeyringDefs;

namespace AWSEncryptionSDK
{
    public class CMMs
    {
        public static CMM MakeDefaultCMM(Keyring keyring)
        {
            DefaultCMM result = new DefaultCMM();
            result.OfKeyring(keyring);
            return result;
        }
    }
}