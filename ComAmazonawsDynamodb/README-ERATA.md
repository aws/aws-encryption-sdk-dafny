# ERATA

This AWS-DDB module is a work in progress, and currently requires some updates in order to successfully build a model and corresponding types with Polymorph.

## Model Modifications

The following updates were made directly to [the model](./Model/dynamodb/model.json).

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

## Generated Smithy->Java Modifications

### Smithy->Java Missing Union Support

The Smithy->Java codegen does not currently handle Union types.
ToNative and ToDafny were modified to include correct conversions for DDB Union types.

### Smithy->Java ToDafny/ToNative missing conversion for Outputs/Inputs

Currently the generated ToDafny only converts DDB Inputs nad ToNative only converts DDB Outputs.
ToNative and ToDanfy were modified so that both performed conversions for both Inputs and Outputs.

### Java type name inconsistencies

The Java name is not always consistent with the smithy name.
The following type names for native types were manually updated:
- InternalServerError -> InternalServerErrorException
- RequestLimitExceeded -> RequestLimitExceededException
- All Input types end with "Request" instead of "Input"
- All Output types end with "Response" instead of "Output"

There is also the following inconsistency for Dafny type names which was manually updated:
- IDynamoDB_20120810Client -> IDynamoDB__20120810Client

### CapacityUnit type inconsistencies

In Smithy ConsumedCapacityUnits are modelled as `integer`, however these fields are Doubles in the Java SDK.
The generated code was manually updated to make Integer and Double conversions in place.
Note that this means that currently information is lost when converting from Java to Dafny.
The API reference specifies that this should be a Double, so this is a case were we should
instead fix the DDB model.

### Not generating CancellationReason/CancellationReasonList

Smithy->Java was not generating CancellationReason/CancellationReasonList, which are modelled in the TransactionCanceledException.
Code to handle this type was manually added.

### AWS SDK Java v2

Smithy->Java did not immediately support v2 names and convensions.
The following changes were made:

- com.amazonaws.services.dynamodbv2 -> software.amazon.awssdk.services.dynamodb
- AmazonDynamoDB -> DynamoDbClient
- Java SDK v2 method name conventions for objects and object Builders (i.e. no "get" or "set).

### AWS SDK Java types for "null" Maps and Lists

Within the SDK, request/response object maps/lists which are not specified get created as types
DefaultSdkAutoConstructMap and DefaultSdkAutoConstructList.
These types eventually get serialized as effectively "None", as opposed to "List/Map with 0 entries".

However, due to our conversions into and out of Dafny, this type information gets lost,
and effectively turns all "unspecified Map/List" into "Map/List with explicitly zero entries".

Thus, our Smithy->Java code generation needs to be smart enough to recognize these special types,
and appropriately represent them as "None" as opposed to "Empty Map/List".

ToDafny conversions were manually updated to check the type information on Maps and Sequences to determine
if the input was this type, and if so represent it as "None" in Dafny.

There may be a better way to handle this discrepency going forward, we should confirm with the SDK team.

