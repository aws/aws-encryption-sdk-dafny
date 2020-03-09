using CMMDefs;
using DefaultCMMDef;
using KeyringDefs;

namespace AWSEncryptionSDK
{
    public class CMMs
    {
        public static CMM MakeDefaultCMM(Keyring keyring)
        {
            DefaultCMM result = new DefaultCMM();
            // TODO: The Dafny constructor shouldn't be directly callable from C# code!
            // In particular, this isn't checking for a null keyring.
            result.OfKeyring(keyring);
            return result;
        }
    }
}
