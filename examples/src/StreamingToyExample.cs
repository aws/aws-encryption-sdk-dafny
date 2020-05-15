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

        static public void RunUTF8TransformInStreamExample() {
            String fileInput = "tmp/streaming-Transform-input.txt";
            String fileExpected = "tmp/streaming-Transform-expected.txt";

            // Read input file and perform transformation using Dafny Enumerator
            // Note that in this example, we load all of the final message into memory
            string transformedMessage;
            using (FileStream fsSource = new FileStream(fileInput, FileMode.Open, FileAccess.Read))
            {
                using (UTF8TransformInStream utf8Transform = new UTF8TransformInStream(fsSource))
                {
                    using (StreamReader reader = new StreamReader(utf8Transform)) {
                        transformedMessage = reader.ReadToEnd();
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

            Assert.Equal(expected, transformedMessage);
        }

        static public void RunUTF8TransformOutStreamExample() {
            // Hardcode a source file for now
            String fileInput = "tmp/streaming-transform-input.txt";
            String fileExpected = "tmp/streaming-transform-expected.txt";

            // Read input file and perform transformation using Dafny Enumerator
            string transformedMessage;
            MemoryStream toTest = new MemoryStream();
            using (FileStream fsSource = new FileStream(fileInput, FileMode.Open, FileAccess.Read))
            {
                using (UTF8TransformOutStream utf8Transform = new UTF8TransformOutStream(toTest))
                {
                    // Transform the file and move output to the MemoryStream
                    fsSource.CopyTo(utf8Transform);
                    // Read the MemoryStream as a string
                    using (StreamReader reader = new StreamReader(toTest))
                    {
                        // Reset position on MemoryStream so we can read
                        toTest.Position = 0;
                        transformedMessage = reader.ReadToEnd();
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

            Assert.Equal(expected, transformedMessage);
        }

        static void Main(string[] args) {
            RunUTF8TransformInStreamExample();
            RunUTF8TransformOutStreamExample();
        }
    }
}
