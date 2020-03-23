using System.IO;
using System.Numerics;
using Consumers_Compile;

namespace Streams {
  class StreamByteProducer: Producers_Compile.ExternalByteProducer {

    internal readonly Stream stream;

    public StreamByteProducer(Stream stream) {
      this.stream = stream;
    }
    
    public bool HasNext() {
      // TODO-RS: I don't think is universally correct
      return stream.Position < stream.Length;
    }

    public byte Next() {
      var result = stream.ReadByte();
      if (result == -1) {
        throw new Dafny.HaltException("No more bytes available");
      }
      return (byte)result;
    }

    public BigInteger Siphon(ExternalByteConsumer consumer) {
//      if (consumer is StreamByteConsumer sc) {
//        // This is close but doesn't track the number of bytes moved,
//        // nor stop short if there isn't enough capacity in the target
//        stream.CopyTo(sc.stream);
//      } else {
        var result = 0;
        while (HasNext() && consumer.CanAccept()) {
          consumer.Accept(Next());
          result++;
        }
        return new BigInteger(result);
//      }
    }
  }
}