using System;
using System.IO;
using System.Text;
using Xunit;
using System.Linq;

using ibyteseq = Dafny.ISequence<byte>;
using IO;
using STL;
using AWSEncryptionSDK;

namespace StreamingToyExample {

    class StreamingToyExample {

        static public void RunEncryptInStreamExample() {
            String fileInput = "tmp/streaming-encrypt-input.txt";
            String fileExpected = "tmp/streaming-encrypt-expected.txt";

            // Read input file and perform transformation using Dafny Enumerator
            // Note that in this example, we load all of the final message into memory
            string encryptedMessage;
            using (FileStream fsSource = new FileStream(fileInput, FileMode.Open, FileAccess.Read))
            {
                using (EncryptInStream fileEncryptor = new EncryptInStream(fsSource))
                {
                    using (StreamReader reader = new StreamReader(fileEncryptor)) {
                        encryptedMessage = reader.ReadToEnd();
                    }
                }
            }
            
            // Read expected output from file
            String expected; 
            using (FileStream fsSource = new FileStream(fileExpected, FileMode.Open, FileAccess.Read))
            {
                // Read bytes as UTF-8
                using (StreamReader reader = new StreamReader(fsSource))
                {
                    expected = reader.ReadToEnd();
                }
            }

            Assert.Equal(expected, encryptedMessage);
        }

        static public void RunEncryptOutStreamExample() {
            // Hardcode a source file for now
            String fileInput = "tmp/streaming-encrypt-input.txt";
            String fileExpected = "tmp/streaming-encrypt-expected.txt";

            // Read input file and perform transformation using Dafny Enumerator
            string encryptedMessage;
            MemoryStream toTest = new MemoryStream();
            using (FileStream fsSource = new FileStream(fileInput, FileMode.Open, FileAccess.Read))
            {
                using (EncryptOutStream fileEncryptor = new EncryptOutStream(toTest))
                {
                    // Encrypt the file and move output to the MemoryStream
                    fsSource.CopyTo(fileEncryptor);
                    // Read the MemoryStream as a string
                    using (StreamReader reader = new StreamReader(toTest))
                    {
                        // Reset position on MemoryStream so we can read
                        toTest.Position = 0;
                        encryptedMessage = reader.ReadToEnd();
                    }
                }
            }

            // Read expected output from file
            String expected; 
            using (FileStream fsSource = new FileStream(fileExpected, FileMode.Open, FileAccess.Read))
            {
                // Read bytes as UTF-8
                using (StreamReader reader = new StreamReader(fsSource))
                {
                    expected = reader.ReadToEnd();
                }
            }

            Assert.Equal(expected, encryptedMessage);
        }

        static void Main(string[] args) {
            RunEncryptInStreamExample();
            RunEncryptOutStreamExample();
        }
    }
}
