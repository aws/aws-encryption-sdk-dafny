namespace aws.crypto


use aws.polymorph#reference
use aws.polymorph#positional

///////////////////
// Basic structures

string KmsKeyId

list KmsKeyIdList {
    member: KmsKeyId
}

string Region

list RegionList {
    member: Region
}


//////////
// Clients


// TODO: Need to discuss with Smithy the best way of referencing this.
// The general idea is that KMS is already modeled in Smithy, so we should
// just be able to refer to the client from that model. The question is what
// exactly that looks like. For now I've chosen a fairly arbitrary string
// from the KMS Smithy model.
// https://github.com/aws/aws-models/blob/master/kms/smithy/model.json#L4849
// https://github.com/aws/aws-models/blob/master/kms/smithy/model.json#L5000
//@reference(service: com.amazonaws.kms#TrentService)
structure KmsClientReference {}

///////////////////
// Client Suppliers
resource ClientSupplier {
    operations: [GetClient]
}

@reference(resource: ClientSupplier)
structure ClientSupplierReference {}

operation GetClient {
    input: GetClientInput,
    output: GetClientOutput,
}

structure GetClientInput {
    @required
    region: Region
}

@positional
structure GetClientOutput  {
    client: KmsClientReference
}
