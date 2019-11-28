package reasoner;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDataProperty;
import org.semanticweb.owlapi.model.OWLDatatype;
import org.semanticweb.owlapi.model.OWLDeclarationAxiom;
import org.semanticweb.owlapi.model.OWLEntity;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.SWRLAtom;
import org.semanticweb.owlapi.model.SWRLRule;
import org.semanticweb.owlapi.profiles.OWL2ELProfile;
import org.semanticweb.owlapi.profiles.OWLProfileReport;

public class Filter {
	public static OWL2ELProfile profileChecker = new OWL2ELProfile();
	public static OWLOntologyManager manager = OWLManager.createOWLOntologyManager();
	public static OWLDataFactory dataFactory = manager.getOWLDataFactory();

	public static Set<OWLAxiom> filterDataAndAnnotationAxioms(Set<OWLAxiom> axioms)
			throws OWLOntologyCreationException {
		Set<OWLAxiom> filteredAxioms = new HashSet<OWLAxiom>();

		for (OWLAxiom axiom : axioms) {
			boolean relevantAxiom = true;

			// Check OWLDataProperty occurrences
			Set<OWLDataProperty> dataProperties = axiom.dataPropertiesInSignature().collect(Collectors.toSet());
			if (!dataProperties.isEmpty())
				relevantAxiom = false;

			// Check OWLDatatype occurrences
			Set<OWLDatatype> datatypes = axiom.datatypesInSignature().collect(Collectors.toSet());
			if (!datatypes.isEmpty())
				relevantAxiom = false;

			// Check valid SWRLRules
			if (axiom.isOfType(AxiomType.SWRL_RULE)) {
				SWRLRule ruleAxiom = (SWRLRule) axiom;
				Set<SWRLAtom> ruleAtoms = ruleAxiom.body().collect(Collectors.toSet());
				ruleAtoms.addAll(ruleAxiom.head().collect(Collectors.toSet()));
				for (SWRLAtom ruleAtom : ruleAtoms)
					if (!(ruleAtom.getPredicate() instanceof OWLClass)
							&& !(ruleAtom.getPredicate() instanceof OWLObjectProperty))
						relevantAxiom = false;
			}

			// Check EL membership
			if (!axiom.isOfType(AxiomType.SWRL_RULE)) {
				Set<OWLAxiom> singleAxiomSet = new HashSet<OWLAxiom>();
				singleAxiomSet.add(axiom);
				singleAxiomSet.addAll(declarationAxioms(axiom));
				OWLOntology singletonOntology = manager.createOntology(singleAxiomSet);
				OWLProfileReport report = profileChecker.checkOntology(singletonOntology);
				if (!report.isInProfile())
					relevantAxiom = false;
			}

			// // Check AnnotationAxiom
			// if (axiom.getAxiomType().equals(AxiomType.ANNOTATION_ASSERTION)
			// || axiom.getAxiomType().equals(AxiomType.ANNOTATION_PROPERTY_DOMAIN)
			// || axiom.getAxiomType().equals(AxiomType.ANNOTATION_PROPERTY_RANGE)
			// || axiom.getAxiomType().equals(AxiomType.SUB_ANNOTATION_PROPERTY_OF))
			// relevantAxiom = false;
			//
			// // Check non-logical axiom
			// if (!axiom.isLogicalAxiom())
			// relevantAxiom = false;

			if (relevantAxiom)
				filteredAxioms.add(axiom);
			else
				System.out.println("WARNING!!! The following axiom is ignored." + "\n" + " > "
						+ axiom.getAxiomType().toString() + "\n" + " > " + axiom + "\n");
		}

		return filteredAxioms;
	}

	private static Collection<OWLDeclarationAxiom> declarationAxioms(OWLAxiom axiom) {
		Set<OWLEntity> entitiesInAxiom = new HashSet<OWLEntity>();
		entitiesInAxiom.addAll(axiom.classesInSignature().collect(Collectors.toSet()));
		entitiesInAxiom.addAll(axiom.objectPropertiesInSignature().collect(Collectors.toSet()));
		entitiesInAxiom.addAll(axiom.individualsInSignature().collect(Collectors.toSet()));

		Set<OWLDeclarationAxiom> declarationAxioms = new HashSet<OWLDeclarationAxiom>();
		for (OWLEntity entity : entitiesInAxiom)
			declarationAxioms.add(dataFactory.getOWLDeclarationAxiom(entity));

		return declarationAxioms;
	}

}
