using System;
using System.IO;
using ToyUTF8Transform;
using IO;
using STL;
using ibyteseq = Dafny.ISequence<byte>;

namespace AWSEncryptionSDK
{
    // EncryptInStream maps a readable C# Stream to a Dafny BytesEnumerator
    // which wraps another readable C# Stream.
    // TODO implement IDisposable
    public class EncryptInStream : Stream {
        // TODO: Implement ReadByte()

        readonly private ToyEnumerator encryptor;
        readonly private Stream sourceStream;
        private MemoryStream outBuffer;
        // We ust maintain EOF state here if interface errors on read after EOF
        private bool atEOF;

        public EncryptInStream(Stream sourceStream) {
            if (!sourceStream.CanRead) {
                throw new ArgumentException("Source stream supplied does not support reading");
            }
            this.sourceStream = sourceStream;

            // Set up the ToyEnumerator to work with the source stream
            // The way we do this is weird, using a C# constructor for the extern and the generated constructor
            // for the ToyEnumerator, but I'm not sure if we'll be able to avoid it
            var externWrapper = new ExternBytesEnumerator(sourceStream);
            var encryptor = new ToyEnumerator();
            encryptor.__ctor(externWrapper);

            this.encryptor = encryptor;
            this.outBuffer = new MemoryStream(); // TODO the way I use MemoryStream is hacky, update to use byte[] efficiently?
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
            if (outBuffer.Length - outBuffer.Position <= 0) {
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
            // TODO if readLen is 0 here something is v wrong
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

        protected override void Dispose(bool disposing)
        {
            // Note: the sinkStream is NOT dispoed if this object is, and anyone using this Stream must appropriately close it
            // TODO any disposing specific logic?
            // TODO what should we do if this closes early? Fail because they don't have a valid ciphertext?
            // TODO should we also deallocate other managed resources, like the outBuffer?
            try {
                // TODO even if not disposing?
                if (!atEOF) {
                    // TODO create the right exception for this
                    throw new Exception("EncryptStream closed before encryption finished.");
                }
            }
            finally {
                base.Dispose(disposing);
            }
        }

    }

    // EncryptOutStream maps a readable C# Stream to a Dafny BytesEnumerator
    // which wraps another readable C# Stream.
    // TODO implement IDisposable, should call End() on Dispose?
    public class EncryptOutStream : Stream {
        // TODO: Implement WriteByte()

        readonly private ToyAggregator encryptor;
        readonly private Stream sinkStream;

        public EncryptOutStream(Stream sinkStream) {
            if (!sinkStream.CanWrite) {
                // TODO find the right or define new Exception type
                throw new NotSupportedException("Source stream supplied does not support writing");
            }
            this.sinkStream = sinkStream;

            // This is some weirdness, but I'm not sure if we'll be able to avoid it
            var externWrapper = new ExternBytesAggregator(sinkStream);
            var encryptor = new ToyAggregator();
            encryptor.__ctor(externWrapper);

            this.encryptor = encryptor;
        }

        public override bool CanRead
        {
            get
            {
                return false;
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
                return true;
            }
        }

        public override void Flush()
        {
          // MUST flush the underlying stream. This means that we must flush the underlying encryptor.
          // In our case, we need to indicate End, as having data buffered means that we require more
          // data in order to be valid. Without that data we are in a bad state. End() will appropraitely
          // return an error. Otherwise, this will signal end and flush the sink Stream.
          // TODO: What would foo being false mean?
          bool foo = DafnyFFI.ExtractResult(encryptor.End());
          sinkStream.Flush();
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
            throw new NotSupportedException();
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
            // TODO what does false foo mean?
            var foo = DafnyFFI.ExtractResult(encryptor.Accept(DafnyFFI.SequenceFromByteArray(buffer, offset, count)));
        }
        
        // The sinkStream is NOT managed by this object, and anyone using this Stream must appropriately close it
        protected override void Dispose(bool disposing)
        {
            try {
                // Release managed resources in encryptor by calling End(). In the ToyExample case, if
                // there is anything in the buffer, we should error, because the bytes inputted
                // were not valid UTF8. In the decrypt case, we want this sort of thing to happen
                // if the user tries to end the stream before getting to the message signature. Ideally we
                // would zero out the plaintext returned if we could, but in this case those bytes are out of
                // our hands :( and into the outStream
                // TODO disposing vs. not disposing?
                // TODO: What would foo being false mean?
                bool foo = DafnyFFI.ExtractResult(encryptor.End());
            } finally {
                base.Dispose(disposing);
            }
        }
    }
}
