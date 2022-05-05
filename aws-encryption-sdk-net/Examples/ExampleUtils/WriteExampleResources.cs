using System.IO;
using static ExampleUtils.ExampleUtils;

namespace ExampleUtils
{
    public static class WriteExampleResources
    {
        public static void EncryptAndWrite(MemoryStream plaintext, string kmsKeyArn, string fileName)
        {
            var ciphertext = EncryptMessageWithKMSKey(plaintext, kmsKeyArn);
            WriteMessage(ciphertext, fileName);
        }
    }
}
