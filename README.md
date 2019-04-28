# Zadanie 1 - Teoria Współbieżności

## Initial model

The first approach was to model the system such way that the nonces (X, Y) are radomly selected from range of predefined values and the message itself consist of 2-element array of bytes. Such model is hard to work with as we do not need to know exact values of nonces, but rather we care about the fact of knowing them. It also have a lot of flaws as it was the very first approach of mine to modeling in Pamela language.
(The model is available in file `initial_model.pml`)

## Improving the model

For simplicity we assume that for now all parts of key-exchange algorithm do not communicate with certificate provider (all public keys are known to everyone). That assumption clarifies all MSC diagrams and reduces trivial code.

The basic model with A, B and basic interceptor C (who passes messages transparently) is present in the file.

![Basic mitm model](https://github.com/styczynski/Needham-Schroeder-promela/blob/master/img/model_image1.png?raw=true)
