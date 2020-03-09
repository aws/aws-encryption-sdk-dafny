using System;
using System.IO;
using ESDKClient;
using STL;

namespace Streams {
    // What's used internally and exposes externally should be different... Right now the C# interface
    // is used for both
    // TODO implement Disposable, wrap stream in friendly handlers
    public partial class OutputStream : Stream {
        // TODO what should the underlying stream actually be?
        // TODO should be readonly
        private ESDKClient.EncryptorStream stream;

        public OutputStream(ESDKClient.EncryptorStream stream) {
            this.stream = stream;
        }

        public override bool CanRead
        {
            get
            {
                return true;
            }
        }

        public override bool CanSeek
        {
            get
            {
                return false;
            }
        }

        public override bool CanWrite
        {
            get
            {
                return false;
            }
        }

        public override void Flush()
        {
          // Do nothing. Docs say to do this instead of throw because it should be valid to flush a readonly stream
        }

        public override long Length
        {
            get
            {
                throw new NotSupportedException();
            }
        }

        public override long Position
        {
            get
            {
                throw new NotSupportedException();
            }
            set
            {
                throw new NotSupportedException();
            }
        }

        public override int Read(byte[] buffer, int offset, int count)
        {
            int n = 0;
            while (n < count) {
                Option<byte> readByte = DafnyFFI.ExtractResult(stream.ReadByte());
                // Replace with Dafny FFI helper
                if (readByte is Option_None<byte> none) {
                    // we've reached the end and can't read any more
                    return n;
                } else if (readByte is Option_Some<byte> some) {
                    // Oof, this is dangerous. Use a helper.
                    buffer[offset+n] = some.get;
                    n += 1;
                } else {
                    throw new ArgumentException(message: "Unrecognized STL.Option constructor");
                }
            }
            return n;
        }

        public override long Seek(long offset, SeekOrigin origin)
        {
            throw new NotSupportedException();
        }

        public override void SetLength(long value)
        {
            throw new NotSupportedException();
        }

        public override void Write(byte[] buffer, int offset, int count)
        {
            throw new NotSupportedException();
        }
    }

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
    }
}
