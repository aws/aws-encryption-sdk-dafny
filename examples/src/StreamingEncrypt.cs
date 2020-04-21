using System;
using System.IO;
using Xunit;
using System.Linq;

using ibyteseq = Dafny.ISequence<byte>;
using IO;
using STL;
using AWSEncryptionSDK;

namespace StreamingEncrypt {

    class StreamingEncrypt {

        public static void EncryptExample(string fileInput) {            
            MemoryStream toTest = new MemoryStream();
            // Read input file using Dafny Enumerator
            using (FileStream fsSource = new FileStream(fileInput, FileMode.Open, FileAccess.Read))
            {
                var fileEncryptor = new EncryptStream(fsSource);
                // No work sad times :'(
                fileEncryptor.CopyTo(toTest);
            }
            
            MemoryStream expected = new MemoryStream();
            // Read input file using C# streaming interface
            using (FileStream fsSource = new FileStream(fileInput, FileMode.Open, FileAccess.Read))
            {
               fsSource.CopyTo(expected);
            }

            // Ensure they are the same
            // TODO compare in a less clunky way
            var msArray1 = expected.ToArray();
            var msArray2 = toTest.ToArray();

            Assert.True(msArray1.SequenceEqual(msArray2));
        }

        static void Main(string[] args) {
            // Hardcode a source file for now
            String fileInput = "tmp/streaming-encrypt-input.txt";
            EncryptExample(fileInput);  
        }
    }
}
