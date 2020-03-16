using System;
using System.IO;
using ESDKClient;
using STL;

namespace Streams {
    public partial class InputStream {
        readonly private Stream stream;

        public InputStream(Stream stream) {
            this.stream = stream;
        }

        public int Read(Dafny.ISequence<byte> bytes, int offset, int count) {
            // TODO handle errors
            int n = stream.Read(bytes.Elements, offset, count);
            return n;
        }

        public int Length() {
            // TODO cutting off int sizes
            return (int)stream.Length;
        }

        public int Position() {
            // TODO cutting off int sizes
            return (int)stream.Position;
        }
    }
}
