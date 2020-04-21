using System;
using System.IO;
using IO;
using STL;
using ibyteseq = Dafny.ISequence<byte>;

namespace AWSEncryptionSDK
{
    // EncryptStream maps a readable C# Stream to a Dafny BytesEnumerator
    // which wraps another readable C# Stream.
    // TODO implement IDisposable
    public class EncryptStream : Stream {

        readonly private EncryptEnumerator encryptor;
        readonly private Stream sourceStream;
        private MemoryStream outBuffer;
        // We ust maintain EOF state here if interface errors on read after EOF
        private bool atEOF;

        public EncryptStream(Stream sourceStream) {
            if (!sourceStream.CanRead) {
                // TODO find the right or define new Exception type
                throw new NotSupportedException("Source stream supplied does not support reading");
            }
            this.sourceStream = sourceStream;

            // This is some weirdness, but I'm not sure if we'll be able to avoid it
            var externWrapper = new ExternBytesEnumerator(sourceStream);
            var encryptor = new EncryptEnumerator();
            encryptor.__ctor(externWrapper);

            this.encryptor = encryptor;
            this.outBuffer = new MemoryStream();
            this.atEOF = false;
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
          // Do nothing. Docs say to do this instead of throw because
          // it should be valid to flush a readonly stream
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
            if (atEOF) {
                // 0 indicates EOF for C# read
                return 0;
            }
            
            // If outBuffer is empty, we should fill it
            if (outBuffer.Length <= 0) {
                Option<ibyteseq> opt = DafnyFFI.ExtractResult(encryptor.Next());
                if (opt is Option_None<ibyteseq> none) {
                    atEOF = true;
                    return 0;
                } else if (opt is Option_Some<ibyteseq> bytes) {
                    // copy returned elements into the outBuffer
                    outBuffer = new MemoryStream(bytes.get.Elements);
                } else {
                    throw new ArgumentException(message: "Unrecognized STL.Option constructor");
                }
            }
            // TODO what error states might we want
            // to handle when wrapping a C# Read?
            var readLen = outBuffer.Read(buffer, offset, count);
            return readLen;
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
}
