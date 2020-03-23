using System.IO;

namespace Streams {
    public class StreamByteConsumer: Consumers_Compile.ByteConsumer {

        internal readonly Stream stream;

        public StreamByteConsumer(Stream stream) {
            this.stream = stream;
        }
        
        public bool CanAccept() {
            // TODO-RS: I don't think is universally correct
            return stream.Position < stream.Length;
        }

        public void Accept(byte b) {
            stream.WriteByte(b);
        }
    }
}