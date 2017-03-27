//   SHACL RDF shape checker
//
// This is or was https://linkeddata.github.io/shacl-check

const $rdf = require('rdflib')
const RDF = $rdf.Namespace('http://www.w3.org/1999/02/22-rdf-syntax-ns#')
const sh = $rdf.Namespace('http://www.w3.org/ns/shacl#')
const a = RDF('type')

// see sh:nodeKind for these values
const termTypeMap = {'NamedNode': 'IRI'}


class ShapeChecker {
  constructor (kb, shapeDoc, targetDoc, reportDoc, options) {
    this.kb = kb
    this.shapeDoc = shapeDoc
    this.targetDoc = targetDoc
    this.reportDoc = reportDoc
    this.options = options || {}
    if (reportDoc) {
      this.report = this.kb.bnode()
      // this.report = this.kb.sym(reportDoc.uri + '#this')
      this.kb.add(this.report, a, sh('ValidationReport'), this.reportDoc)
    } else {
      console.log("ShapeChecker: NO REPORT DOCUMENT GIVEN")
    }
  }

  complain (message) {
    console.log(message)
  }

  validationResult (params, message) {
    this.conforms = false
    if (this.reportDoc) {
      let result = this.kb.bnode()
      this.kb.add(this.report, sh('result'), result, this.reportDoc)
      this.kb.add(result, a, sh('ValidationResult'), this.reportDoc)
      this.kb.add(result, sh('focusNode'), params.node, this.reportDoc)
      this.kb.add(result, sh('sourceShape'), params.shape, this.reportDoc)
      if (params.path) this.kb.add(result, sh('resultPath'), params.path, this.reportDoc)
      if (params.object !== undefined) {
        this.kb.add(result, sh('value'), params.object, this.reportDoc)
      }
      this.kb.add(result, sh('resultMessage'), message, this.reportDoc)
      let severity = this.kb.any(params.shape, sh('severity')) || sh('Violation')
      this.kb.add(result, sh('resultSeverity'), severity, this.reportDoc)
      this.kb.add(result, sh('sourceConstraintComponent'), sh(params.cc + 'ConstraintComponent'), this.reportDoc)
    }
  }

  // Find any shapes which should be applied to nodes
  execute () {
    const checker = this
    const kb = this.kb
    const post = function (issues) {
      if (!issues) return
      for (let i=0; i< issues.length; i++) {
        checker.validationResult(issues[i].params, issues[i].message)
      }
    }
    kb.statementsMatching(null, sh('targetClass'), null, this.shapeDoc)
    .forEach(function (st) {
      var targetClass = st.object
      var shape = st.subject
      console.log("Target class " + targetClass)
      kb.each(null, a, targetClass).forEach(function (target) {
        console.log("Target class member " + target)
        post(checker.checkNodeShape(target, shape))
      })
    })
    kb.statementsMatching(null, sh('targetNode'), null, this.shapeDoc)
    .forEach(function (st) {
      var target = st.object
      var shape = st.subject
      console.log("Target node " + target)
      post(checker.checkNodeShape(target, shape))
    })

    if (this.reportDoc) {
      kb.add(this.report, sh('conforms'), this.conforms, this.reportDoc)
    }
  }

  // Return an array of nodes at the end of the path
  followPath (node, path) {
    let pred = this.kb.any(path, sh('inversePath'))
    if (pred) {
      return this.kb.each(null, pred, node)
    }

    if (path.termType === 'Collection') { // A base list is a sequence
      var results = []
      var followSeq = function (node, array) {
        if (array.length === 0) {
          results = results.push(node)
        }
        this.followPath(node, array[0]).forEach(function (next) {
          followSeq(next, path.slice(1))
        })
      }
      followSeq(path.elements)
      return results
    }

    let alt = this.kb.any(path, a, sh('alternative'))
    if (alt) {
      let results = []
      for (let i = 0; i < alt.length; i++) {
        results = results.concat(this.followPath(alt.elements[i]))
      }
      return results
    }

    let sub = this.kb.any(path, a, sh('oneOrMorePath'))
    if (sub) {
      let soFar = this.followPath(node, sub)
      if (soFar.length === 0) {
        this.complain('Sould be at least one')
      }
      return soFar
    }

    sub = this.kb.any(path, a, sh('zeroOrMorePath'))
    if (sub) {
      let soFar = this.followPath(node, sub)
      // if (soFar.length ) // Semantics if this?
      return soFar
    }

    sub = this.kb.any(path, a, sh('zeroOrOnePath'))
    if (sub) {
      let soFar = this.followPath(node, sub)
      if (soFar.length > 1) {
        this.complain('Sould be no more than one')
      }
      return soFar
    }

    // default is this is just a forward predicate
    return this.kb.each(node, path)
  }

  // Returns an array of issues else false
  //
  checkNodeShape (node, shape) {
    const kb = this.kb
    const checker = this
    console.log(" Applying shape " + shape)
    console.log("        to node " + node)

    var closed = kb.anyValue(shape, sh('closed'))
    closed = {'true': true, '1':true}[closed] || false
    console.log('  closed: ' + closed)
    if (closed) {
      var allowed = []
      var ignoredProperties = kb.any(shape, sh('ignoredProperties'))
      if (ignoredProperties){
        ignoredProperties = ignoredProperties.elements
        for (let k=0; k < ignoredProperties.length; k++){
          console.log('      Ignoreable: ' + ignoredProperties[k])
          allowed[ignoredProperties[k].uri] = true
        }
      }
    }
    var issues = []
    const noteIssue = function (params, message) {
      console.log('  -> ' + message)
      issues.push({ params: params, message: message })
    }
    kb.each(shape, sh('property')).forEach(function (property) {

      let path = kb.the(property, sh('path')) // Assume simple predicate at this stage
      console.log("  Checking property " + property + ': ' + path)
      let values = checker.followPath(node, path)
      if (path.uri) {
        allowed[path.uri] = true
      }

      let minCount = kb.anyValue(property, sh('minCount'))
      if (minCount && values.length < minCount) {
        noteIssue({node, shape, cc:'MinCount'}, 'Too few (' + values.length + ') '  + path + ' on ' + node)
      }
      let maxCount = kb.anyValue(property, sh('maxCount'))
      if (maxCount && values.length > maxCount) {
        noteIssue({node, shape, cc:'MaxCount'}, 'Too many (' + values.length + ') ' + path + ' on ' + node)
      }
      let constraint

      for (var i = 0; i < values.length; i++) {
        let object = values[i]

        /////// Checking for object class membership

        let constraints = kb.each(property, sh('class'))
        if (constraints) {
          constraints.forEach(function (constraint) {
            if (constraint && !kb.holds(object, a, constraint)) {
              noteIssue({node, shape, cc: 'Class'}, 'Error ' + object + ' should be in class ' + constraint)
            }
          })
        }

        //////////////////////////////// Comparing with other predicates

        constraint = kb.anyValue(property, sh('equals'))
        if (constraint) {
          let others = kb.each(node, constraint) // @@ extend to general paths??
          for (let k=0; k<others.length; k++) {
            if (!object.sameTerm(others[k])){
              noteIssue({node, shape, object, cc: 'Equals'}, 'Error ' + object + ' should be equal to ' + constraint + ' that is, ' + others[k])
            }
          }
        }
        constraint = kb.anyValue(property, sh('disjoint'))
        if (constraint) {
          let others = kb.each(node, constraint) // @@ extend to general paths??
          for (let k=0; k<others.length; k++){
            if (object.sameTerm(others[k])){
              noteIssue({node, shape, object, cc: 'Equals'}, 'Error ' + object + ' should be NOT equal to ' + constraint + ' that is, ' + others[k])
            }
          }
        }
        // @@ todo:  LessThan etc etc

        ///////////////////////////// Range constraints

        constraint = kb.anyValue(property, sh('minInclusive'))
        if (constraint && !(object.value && object.value >= constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, object, cc: 'MinInclusive'}, 'Error ' + object + ' should more than or equal to  ' + constraint)
        }
        constraint = kb.anyValue(property, sh('minExclusive'))
        if (constraint && !(object.value && object.value > constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, object, cc:'MinExclusive'}, 'Error ' + object + ' should more than ' + constraint)
        }
        constraint = kb.anyValue(property, sh('maxInclusive'))
        if (constraint && !(object.value && object.value <= constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, object, cc: 'MaxInclusive'}, 'Error ' + object + ' should less than or equal to  ' + constraint)
        }
        constraint = kb.anyValue(property, sh('maxExclusive'))
        if (constraint && !(object.value && object.value < constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, object, cc: 'MaxExclusive'}, 'Error ' + object + ' should less than or equal to  ' + constraint)
        }
        constraint = kb.anyValue(property, sh('minLength'))
        if (constraint && !(object.value && object.value.length < constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, object, cc: 'MinLength'}, 'Error ' + object + ' should less than or equal to  ' + constraint)
        }
        constraint = kb.anyValue(property, sh('maxLength'))
        if (constraint && !(object.value && object.value.length > constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, object, cc: 'MexLength'}, 'Error ' + object + ' should less than or equal to  ' + constraint)
        }

        //////////////////////////////////  Others

        constraint = kb.any(property, sh('datatype'))
        if (constraint && !(object.datatype && object.datatype.sameTerm(constraint))) {
          noteIssue({node, shape, object, cc: 'Datatype'}, 'Error ' + object + ' should be datatype  ' + constraint)
        }
        constraint = kb.anyValue(property, sh('languageIn'))
        if (constraint) {
          let langs = constraint.elements.map(function (x) {return x.value}).join(',')
          if (!(object.lang && langs.includes(object.lang))) {
            noteIssue({node, shape, object, cc: 'LanguageIn'}, 'Error ' + object + ' should be in one of languages: ' + langs)
          }
        }
        constraint = kb.anyValue(property, sh('pattern'))
        if (constraint) {
          if (!(object.value && object.value.match(constraint))) {
           noteIssue({node, shape, object, cc: 'Pattern'}, 'Error ' + object + ' should match pattern  ' + constraint)
         }
        }
        constraint = kb.any(property, sh('nodeKind'))
        if (constraint) {
          let actual = termTypeMap[object.termType] || object.termType
          let allowed = constraint.uri.split('#')[1] // eg 'BlankNodeOrIRI'
          if (!allowed.includes(actual)) {
            noteIssue({node, shape, object, cc: 'NodeKind'}, 'Error ' + object + ' should be of node kind:  ' + constraint)
          }
        }

        ////////////////////// Logical ones

        constraint = kb.any(property, sh('node'))
        if (constraint && !(checkNodeShape(object, constraint))) {
          noteIssue({node, shape, object, cc: 'Not'}, 'Error ' + object + ' should match shape  ' + constraint)
        }
        constraint = kb.any(property, sh('not'))
        if (constraint && (checkNodeShape(object, constraint))) {
          noteIssue({node, shape, object, cc: 'Not'}, 'Error ' + object + ' should NOT match shape  ' + constraint)
        }
        // @@ add adnd, or, xone

        // end of tests
      } // next value
    }) // next property
    if (closed){
      let failed = false
      kb.statementsMatching(node).forEach(function (st) {
        if (!allowed[st.predicate.uri]){
          noteIssue({shape, node, object: st.object, cc: 'Closed'}, 'Closed node has extra data: ' + st)
        }
      })
    }
    return issues.length ? issues : false
  } // method
} // End of class ShapeChecker

module.exports = ShapeChecker

// //////////////////////////////
