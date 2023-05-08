# DDB Model

This directory contains the [DDB smithy model](https://github.com/aws/aws-models/blob/08febb37e86e45dbe0069b69f81ba01d8579eb2e/dynamodb/smithy/model.json),
but with a couple adjustments:

### Operation Changes

The following operations defined in the model have colliding input and 
output structures.
- `DisableKinesisStreamingDestination`
- `EnableKinesisStreamingDestination`

Both opertations are defined to use the input and output structures
- `KinesisStreamingDestinationInput`
- `KinesisStreamingDestiantinOutput`

In the aws sdk net v3 of the [AWS SDK NET for DynamoDB](https://docs.aws.amazon.com/sdkfornet/v3/apidocs/items/DynamoDBv2/NDynamoDBv2Model.html), 
the Kinesis Streaming Destination operations do not share input and output structures;
however, the model definition did not change for backwards compatability reasons. 

Our code generation did not know how to make this distinction. 
In order to support DynamoDBv2, we changed the model definition to better reflect this change. 
NOTE: The original KinesisStreamingDestinationInput/Output structures were not deleted from 
the model

We modified the Operations input/output structures as follows:
```
"com.amazonaws.dynamodb#DisableKinesisStreamingDestination": {
    ...
    "input": { "target": "com.amazonaws.dynamodb#DisableKinesisStreamingDestinationInput"}, 
    "output": { "target": "com.amazonaws.dynamodb#DisableKinesisStreamingDestinationOutput"},
    ...
},
"com.amazonaws.dynamodb#EnableKinesisStreamingDestination": {
    ...
    "input": { "target": "com.amazonaws.dynamodb#EnableKinesisStreamingDestinationInput"}, 
    "output": { "target": "com.amazonaws.dynamodb#EnableKinesisStreamingDestinationOutput"},
    ... 
}
```

The new modeled structures:
- DisableKinesisStreamingDestinationInput
- DisableKinesisStreamingDestinationOutput
- EnableKinesisStreamingDestinationInput
- EnableKinesisStreamingDestinationOutput

Have the same definition as:
- KinesisStreamingDestinationInput
- KinesisStreamingDestinationOutput
