# Zadanie 1 - Teoria Współbieżności

## Initial model

The first approach was to model the system such way that the nonces (X, Y) are radomly selected from range of predefined values and the message itself consist of 2-element array of bytes. Such model is hard to work with as we do not need to know exact values of nonces, but rather we care about the fact of knowing them. It also have a lot of flaws as it was the very first approach of mine to modeling in Pamela language.

The model is available in file [prototype.pml](https://github.com/styczynski/Needham-Schroeder-promela/blob/master/src/prototype.pml)

## Improving the model

For simplicity we assume that for now all parts of key-exchange algorithm do not communicate with certificate provider (all public keys are known to everyone). That assumption clarifies all MSC diagrams and reduces trivial code.

The basic model with A, B and basic interceptor C (who passes messages transparently) is present in the file [basic_model.pml](https://github.com/styczynski/Needham-Schroeder-promela/blob/master/src/basic_model.pml)

![Basic mitm model](https://github.com/styczynski/Needham-Schroeder-promela/blob/master/img/model_image1.png?raw=true)

## Interceptor knowledge base

| Received message | Additional knowledge |
|------------------|--------------|
| (X, A, C)        | X            |
| (X, A, B)        | (X, A, B)    |
| (X, C)           | X            |
| (Y, C)           | Y            |
| (ANY, C)         | -            |
| (A, C)           | -            |
| (B, C)           | -            |
| (C, C)           | -            |
| (Y, Y, C)        | Y            |
| (ANY, Y, C)      | Y            |
| (X, Y, A)        | (X, Y, A)    |
| (Y, Y, A)        | (Y, Y, A)    |
| (ANY, Y, A)      | (ANY, Y, A)  |
| (A, Y, C)        | Y            |
| (B, Y, C)        | Y            |
| (C, Y, C)        | Y            |
| (A, Y, A)        | (A, Y, A)    |
| (B, Y, A)        | (B, Y, A)    |
| (C, Y, A)        | (C, Y, A)    |
| (X, B)           | (X, B)       |
| (Y, B)           | (Y, B)       |
| (ANY, B)         | (ANY, B)     |
| (A, B)           | (A, B)       |
| (B, B)           | (B, B)       |
| (C, B)           | (C, B)       |

| Sent message | Required knowledge  |
|--------------|---------------------|
| (X, A, B)    | X | (X, A, B)       |
| (X, B, B)    | X | (X, B, B)       |
| (X, C, B)    | X | (X, C, B)       |
| (Y, A, B)    | Y | (Y, A, B)       |
| (Y, B, B)    | Y | (Y, B, B)       |
| (Y, C, B)    | Y | (Y, C, B)       |
| (ANY, A, B)  | -                   |
| (ANY, B, B)  | -                   |
| (ANY, C, B)  | -                   |
| (X, A, A)    | X | (X, A, A)       |
| (X, B, A)    | X | (X, B, A)       |
| (X, C, A)    | X | (X, C, A)       |
| (A, A, B)    | -                   |
| (A, B, B)    | -                   |
| (A, C, B)    | -                   |
| (B, A, B)    | -                   |
| (B, B, B)    | -                   |
| (B, C, B)    | -                   |
| (C, A, B)    | -                   |
| (C, B, B)    | -                   |
| (C, C, B)    | Y | (Y, B)          |
| (Y, B)       | X | (X, X, A)       |
| (X, X, A)    | (X & Y) | (X, Y, A) |
| (X, Y, A)    | X | (X, ANY, A)     |
| (X, ANY, A)  |                     |
