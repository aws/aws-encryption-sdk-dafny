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
            while (stream.HasNext() && n < count) {
                byte readByte = DafnyFFI.ExtractResult(stream.Next());

                // TODO 0 could be a failure or EOF, which is unfortunate.
                // For now just read it as is. Implement proper failures later.
                buffer[offset+n] = readByte;
                n += 1;
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

        public int Position() {
            // TODO cutting off int sizes
            return (int)stream.Position;
        }
    }
}
