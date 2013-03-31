/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact;

/**
 * It performs a change dependency analysis for modifiability (as implemented by 
 * class ChangeImpactAnalyzer). This is a 'full-fledged' reasoning framework, because
 * it is able to analyze the architecture and also propose tactics to improve  
 * the responses of scenarios. Two sample tactics are supported: split a 
 * responsibility with high cost, and insert and intermediary for a module that
 * has a strong coupling with other modules in the view.
 * 
 * @author Andres Diaz-Pace
 */

import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URL;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.List;
import java.util.logging.Level;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;

import arche.modifChangeImpact.hibernate.ArchECoreArchitecture;
import arche.modifChangeImpact.hibernate.ArchECoreResponsibilityStructure;
import arche.modifChangeImpact.hibernate.vo.ArchEModuleVO;
import arche.modifChangeImpact.hibernate.vo.ArchEObjectVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityDependencyRelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityVO;
import arche.modifChangeImpact.hibernate.vo.ArchEScenarioVO;
import arche.modifChangeImpact.hibernate.vo.ArchETranslationRelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;

import edu.cmu.sei.arche.ArchEException;

import edu.cmu.sei.arche.external.data.ArchEArchitecture;
import edu.cmu.sei.arche.external.data.ArchERelation;
import edu.cmu.sei.arche.external.data.ArchERequirementModel;
import edu.cmu.sei.arche.external.data.ArchEResponsibility;
import edu.cmu.sei.arche.external.data.ArchEResponsibilityStructure;
import edu.cmu.sei.arche.external.data.ArchEScenario;
import edu.cmu.sei.arche.external.data.ArchEView;

import edu.cmu.sei.arche.external.reasoningframework.ArchEAnalysisProblem;
import edu.cmu.sei.arche.external.reasoningframework.ArchEAnalysisResult;
import edu.cmu.sei.arche.external.reasoningframework.ArchEEvaluationResult;
import edu.cmu.sei.arche.external.reasoningframework.ArchEReasoningFramework;
import edu.cmu.sei.arche.external.reasoningframework.ArchETryTacticResult;
import edu.cmu.sei.arche.external.reasoningframework.ArchEUserQuestion;
import edu.cmu.sei.arche.external.reasoningframework.RFArchitecturalTransformation;

public class ModifChangeImpactReasoningFramework extends ArchEReasoningFramework {

	// To compute the cost of applying different tactics to different architectures
	private static int ModuleIntermediaryCounter = 1;
	private static int ResponsibilityChildrenCounter = 1;
	
	//---- Names of parameters used by this reasoning framework
	public static final String PARAMETER_COST_OF_CHANGE 		= "P_CostOfChange";
	public static final String PARAMETER_PROBABILITY_INCOMING 	= "P_ProbabilityIncoming";
	public static final String PARAMETER_PROBABILITY_OUTGOING 	= "P_ProbabilityOutgoing";	
	
	//---- Questions and warnings defined in the question file by this reasoning framework
	public static final String SPLIT_RESPONSIBILITY_QUESTION 				= "splitResponsibility";
	public static final String INSERT_INTERMEDIARY_QUESTION 				= "insertIntermediary";
	public static final String ADJUST_REFINED_RESPONSIBILITIES_QUESTION 	= "adjustRefinedResponsibilities";
	public static final String ABSTRACT_COMMON_RESPONSIBILITIES_QUESTION 	= "abstractCommonResponsibilities";
	public static final String FIX_ANALYSIS_PARAMETERS_WARNING 				= "fixAnalysisParameters";
	public static final String DECIDE_ON_SPLITTING_WARNING 					= "decideOnSplitting";

	//---- Tactic names used by this reasoning framework to execute architectural transformations
	public static final String SPLIT_RESPONSIBILITY_TACTIC 						= "SplitResponsibility";
	public static final String INSERT_INTERMEDIARY_MODULE_TACTIC 				= "InsertIntermediary";
	public static final String ADJUST_IMPACT_REFINED_RESPONSIBILITIES_TACTIC 	= "AdjustChangeImpact";
	public static final String ABSTRACT_COMMON_RESPONSIBILITIES_TACTIC 			= "AbstractCommonResponsibilities";

	//---- Modifiability-specific types of errors
	protected static final int WRONG_PROBABILITY_SETTING_ERROR 			= 1;
	protected static final int RESPONSIBILITY_COST_OUT_OF_LIMITS_ERROR 	= 2;
	
	protected static final double INVALID_RESPONSE = Double.MAX_VALUE/2; // An arbitrary high value

	public ModifChangeImpactReasoningFramework() {
		super();
		
		// set data provider
    	setDataProvider(new ChangeImpactModifiabilityRFDataProvider());   	
    	
    	// configure this RF with the configuration file 
		try {     	   
			URL url = FileLocator.find(Platform.getBundle("SEI.ArchE.ModifChangeImpact"), new Path("/config"), null);
			String installPathName = FileLocator.resolve(url).getPath();
			String rfconfigFullPath = installPathName + "modifchangeimpact-rfconfig.xml";
			configure(rfconfigFullPath);
		} catch (MalformedURLException e1){
			e1.printStackTrace();
		} catch (IOException e1){
			e1.printStackTrace();
		}                             
	}

	/**
	 * It starts the interpretation/evaluation based on the change impact analyzer 
	 * (assuming no errors in the process)
	 * 
	 * @param architecture current architecture model (assumed consistent)
	 * @param currentScenario scenario to be analyzed on the architecture
	 * @throws ArchEException
	 */
	@Override
    public ArchEEvaluationResult analyze(ArchEArchitecture architecture, ArchEScenario scenario) throws ArchEException {
		
		// Configuration of the analyzer		
		ModuleADLWrapper adlModel = (ModuleADLWrapper)(architecture.getView());	
		ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)(architecture.getResponsibilityStructure());
		
		List<ArchEResponsibility> responsibilities = coreResponsibilities.getResponsibilitiesByScenario(scenario);
		printLog(2, Level.INFO, "Recovering related responsibilities: " + responsibilities.size() + " - analyze on version= "+architecture.getCurrentVersion().getId());			
		printLog(2, Level.INFO, "Number of responsibility dependencies (structure) --> "+coreResponsibilities.getRelations(ArchEResponsibilityDependencyRelationVO.class.getName()).size());

		double response = INVALID_RESPONSE;
		double responseVal = 0.0; // The minimum possible cost for modifiability
		if (scenario.getMeasureValue() != null)
			responseVal = scenario.getMeasureValue();
		boolean interpretationOk = false;

		printLog(2, Level.INFO, "Running analysis for the scenario \"" + scenario.getDescription() + "\"");			

		if (this.isResponsibilityStructureValid()) {			

			ChangeImpactAnalyzer analyzer = new ChangeImpactAnalyzer(adlModel,coreResponsibilities);

			try {
				interpretationOk = analyzer.doInterpretation(responsibilities);
			} catch (ChangeImpactAnalysisException e) {
				this.setAnalysisStatus(RF_WARNING); // Because it is just an error on the alternative and not in the original architecture
				//this.setAnalysisStatus(RF_ERROR);
				interpretationOk = false;
				//throw new ArchEException(e.getMessage(),e.getCause());
			}
			
			if (interpretationOk) {
				analyzer.doEvaluation();		
				//The different values computed by the analyzer for the scenario
				printLog(3, Level.INFO, "Number of modules in the view --> "+adlModel.getModules().size()+" for "+responsibilities.size()+" primary responsibilities");
				printLog(3, Level.INFO, "Number of module dependencies in the view --> "+adlModel.getCountModuleDependencies());
				printLog(3, Level.INFO, "Scope rate for modules --> "+analyzer.getRatioPrimaryModules()+" (primary ones versus total)");
				printLog(3, Level.INFO, "Scope rate for responsibilities --> "+analyzer.getRatioPrimaryResponsibilities()+" (primary ones versus total)");
				printLog(3, Level.INFO, "Average module cost (initial) --> "+analyzer.getAvgModuleInitialCost());
				printLog(3, Level.INFO, "Average module cost (computed) --> "+ analyzer.getAvgModuleEstimatedCost());
				printLog(3, Level.INFO, "Average responsibility cost (initial) --> "+analyzer.getAvgResponsibilityInitialCost());
				printLog(3, Level.INFO, "Average responsibility cost (computed) --> "+analyzer.getAvgResponsibilityEstimatedCost());
				printLog(3, Level.INFO, "Average module cohesion --> "+analyzer.getAvgModuleCohesion());
				printLog(3, Level.INFO, "Average module coupling --> "+analyzer.getAvgModuleCoupling());		
				printLog(3, Level.INFO, "Average rippling --> "+analyzer.getAvgRipplingProbability());
				
				response = analyzer.getTotalCost();
				if (response == INVALID_RESPONSE) // This value should have no sense for analysis
					this.setAnalysisStatus(RF_WARNING);
				else
					this.setAnalysisStatus(RF_OK);
				if (response < responseVal) { 
					printLog(2, Level.INFO, "Evaluation result = " + response +" (satisfied)"+" reference= "+responseVal);
				}
				else {
					printLog(2, Level.INFO, "Evaluation result = " + response +" (not satisfied)"+" reference= "+responseVal);
				}				

			}	
			else { // the responsibility structure is OK, but the interpretation/evaluation had errors
				printLog(3, Level.INFO, "Interpretation: Error(s) ocurred when setting primary responsibilities ...");			
				printLog(3, Level.INFO, "Evaluation result = " + response);		
				this.setAnalysisStatus(RF_WARNING); // Because it is just an error on the alternative and not in the original architecture
				//this.setAnalysisStatus(RF_ERROR);
			}
		}
		else { // The responsibility structure had problems, so analysis couldn't be performed
			printLog(3, Level.INFO, "Pre-Analysis: Error(s) ocurred when checking the responsibility structure ...");			
			printLog(3, Level.INFO, "Evaluation result = " + response);		
			this.setAnalysisStatus(RF_WARNING); // Because it is just an error on the alternative and not in the original architecture
			//this.setAnalysisStatus(RF_ERROR);			
		}

		ArchEEvaluationResult evaluationResult = new ArchEEvaluationResult();
		evaluationResult.setScenario(scenario.getFactId());
		
		// Set the difference with the value from the previous round of analysis (if any)
		ArchEAnalysisResult previousAnalysisResult = this.restoreAnalysisResult(scenario.getFactId());
		double diff = 0.0;
		if (previousAnalysisResult != null)  
			diff = response - previousAnalysisResult.getValue();
		evaluationResult.setChange(diff);
		
		if (response < responseVal) // This estimation of utility is just a possible example 
			evaluationResult.setUtility(1.0);
		else  if (diff <= 0)
			evaluationResult.setUtility(0.4);
		else
			evaluationResult.setUtility(0.0);

//		RFArchitecturalTransformation lastTactic = this.getLastSuggestedTactic(architecture);
//		if (lastTactic == null) {
//			System.out.println("LAST TACTIC APPLIED (IN ANALYZE): NULL (set to do-nothing)");
//			lastTactic = defaultDoNothingTactic;
//		}
//		else 
//			System.out.println("LAST TACTIC APPLIED (IN ANALYZE): "+lastTactic.toString());
//
//		Double numberOfResources = scenario.getStimulusValue();
//		if (numberOfResources == null)
//			numberOfResources = 1.0;
//		double responseUtility = ChangeImpactAnalyzer.getUtility(response, responseVal, numberOfResources.intValue(), lastTactic);
//		evaluationResult.setUtility(responseUtility);
//
//		if (response < responseVal) // This estimation of utility is just a possible example 
//			evaluationResult.setUtility(1.0);
//		else  if (diff <= 0)
//			evaluationResult.setUtility(0.4);
//		else
//			evaluationResult.setUtility(0.0);		
		
		evaluationResult.setResult(response);
		
		return (evaluationResult);

	}

	/**
	 * It invokes the same analysis than before, but also suggests tactics based
	 * on the result of the analysis (assuming no errors in the process)
	 * 
	 * @param architecture current architecture model (assumed consistent)
	 * @param currentScenario scenario to be analyzed on the architecture
	 * @param outTactics the list of suggested tactics (output parameter)
	 * @throws ArchEException
	 */
	@Override
	public ArchEAnalysisResult analyzeAndSuggest(ArchEArchitecture architecture, ArchEScenario scenario, List<ArchETryTacticResult> outTactics) throws ArchEException {
		
		// Configuration of the analyzer		
		ModuleADLWrapper adlModel = (ModuleADLWrapper)(architecture.getView());	
		ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)(architecture.getResponsibilityStructure());
		ChangeImpactAnalyzer analyzer = new ChangeImpactAnalyzer(adlModel,coreResponsibilities);
			
		List<ArchEResponsibility> responsibilities = coreResponsibilities.getResponsibilitiesByScenario(scenario);
		printLog(2, Level.INFO, "Recovering related responsibilities: " + responsibilities.size() + " - analyze on version= "+architecture.getCurrentVersion().getId());			
		printLog(2, Level.INFO, "Number of responsibility dependencies (structure) --> "+coreResponsibilities.getRelations(ArchEResponsibilityDependencyRelationVO.class.getName()).size());

		double response = INVALID_RESPONSE;
		boolean isScenarioSatisfied = false;
		boolean interpretationOk = false; 
		double responseVal = 0.0;// The minimum possible cost for modifiability
		if (scenario.getMeasureValue() != null)
			responseVal = scenario.getMeasureValue();

		if (this.isResponsibilityStructureValid()) {
			
			try {
				interpretationOk = analyzer.doInterpretation(responsibilities);
			} catch (ChangeImpactAnalysisException e) {
				this.setAnalysisStatus(RF_ERROR);
				interpretationOk = false;
				//throw new ArchEException(e.getMessage(),e.getCause());
			}

			printLog(2, Level.INFO, "Running analysis for the scenario \"" + scenario.getDescription() + "\"");			
			if (interpretationOk){
				analyzer.doEvaluation();	
				// The different values computed by the analyzer for the scenario
				printLog(3, Level.INFO, "Number of modules in the view --> "+adlModel.getModules().size()+" for "+responsibilities.size()+" primary responsibilities");
				printLog(3, Level.INFO, "Number of module dependencies in the view --> "+adlModel.getCountModuleDependencies());
				printLog(3, Level.INFO, "Scope rate for modules --> "+analyzer.getRatioPrimaryModules()+" (primary ones versus total)");
				printLog(3, Level.INFO, "Scope rate for responsibilities --> "+analyzer.getRatioPrimaryResponsibilities()+" (primary ones versus total)");
				printLog(3, Level.INFO, "Average module cost (initial) --> "+analyzer.getAvgModuleInitialCost());
				printLog(3, Level.INFO, "Average module cost (computed) --> "+ analyzer.getAvgModuleEstimatedCost());
				printLog(3, Level.INFO, "Average responsibility cost (initial) --> "+analyzer.getAvgResponsibilityInitialCost());
				printLog(3, Level.INFO, "Average responsibility cost (computed) --> "+analyzer.getAvgResponsibilityEstimatedCost());
				printLog(3, Level.INFO, "Average module cohesion --> "+analyzer.getAvgModuleCohesion());
				printLog(3, Level.INFO, "Average module coupling --> "+analyzer.getAvgModuleCoupling());		
				printLog(3, Level.INFO, "Average rippling --> "+analyzer.getAvgRipplingProbability());				

				response = analyzer.getTotalCost();
				if (response == INVALID_RESPONSE) // This value may have no sense for analysis
					this.setAnalysisStatus(RF_WARNING);
				else
					this.setAnalysisStatus(RF_OK);
				if (response <= responseVal) {
					isScenarioSatisfied = true;
					printLog(2, Level.INFO, "Analysis result = " + response +" (satisfied)"+" reference= "+responseVal);
				}
				else 
					printLog(2, Level.INFO, "Analysis result = " + response +" (not satisfied)"+" reference= "+responseVal);
			
			}
			else { // the responsibility structure is Ok, but the interpretation/evaluation had errors
				printLog(3, Level.INFO, "Interpretation: Error(s) ocurred when setting the primary responsibilities ...");			
				printLog(3, Level.INFO, "Analysis result = " + response);																
				this.setAnalysisStatus(RF_ERROR);
			}
		}
		else { // The responsibility structure had problems, so analysis couldn't be performed
			printLog(3, Level.INFO, "Pre-Analysis: Error(s) ocurred when checking the responsibility structure ...");			
			printLog(3, Level.INFO, "Analysis result = " + response);		
			this.setAnalysisStatus(RF_ERROR);			
		}			
		
		// Here is the suggestion of tactics (in case no errors were found during analysis)		
		if (this.isAnalysisValid() && !isScenarioSatisfied) {
			// Tactics for this reasoning framework are selected (via search), 
			// based on the results of the analysis
			List<ArchETryTacticResult> candidateTactics = this.suggestTacticsBasedOnAnalysis(
					analyzer,responsibilities,coreResponsibilities,adlModel, scenario);

			ArchETryTacticResult tryTactic = null;
			for (Iterator<ArchETryTacticResult> it = candidateTactics.iterator(); it.hasNext();) {
				tryTactic= it.next();
				// Here I configure some remaining parameters for the tactic
				tryTactic.setReasoningFramework(this.getID());
				tryTactic.setScenario(scenario);
				outTactics.add(tryTactic);
				printLog(4, Level.INFO, "tactic --> " + tryTactic.getTacticName());				
			}			
			
			printLog(3, Level.INFO, "Tactics suggested = " + outTactics.size());
		}
		
		ArchEAnalysisResult analysisResult = new ArchEAnalysisResult();
		analysisResult.setValue(response);
		analysisResult.setOwner(scenario.getFactId());
		analysisResult.setReasoningFramework(this.getID());
		analysisResult.setSatisfied(isScenarioSatisfied);
		analysisResult.setQuality(this.getQuality());

		// Set the value from the previous round of analysis (if any)
		ArchEAnalysisResult previousAnalysisResult = this.restoreAnalysisResult(scenario.getFactId());
		if (previousAnalysisResult != null) 
			analysisResult.setOldValue(previousAnalysisResult.getValue());
		else 
			analysisResult.setOldValue(0.0);

		return (analysisResult);

	}

	/**
	 * It creates or updates the module view (before analysis can proceed)
	 * 
	 * @param view an existing module view (not necessarily empty)
	 * @param responsibilityStructure the current responsibility structure
	 * @param requirementModel the current requirement model 
	 * @throws ArchEException
	 */
	@Override
	public boolean initializeView(ArchEView view, ArchEResponsibilityStructure responsibilityStructure, ArchERequirementModel requirementModel) throws ArchEException {
		if(view == null)
			throw new ArchEException("view must be not null");
		
//		return (this.initializeArchETNExampleView(view, responsibilityStructure, requirementModel));
//		return (this.initializeMVCCTASExampleView(view, responsibilityStructure, requirementModel));
//		return (this.initializeBizcoExampleView(view, responsibilityStructure, requirementModel));
		
		boolean changed = false;
		
		printLog(1, Level.INFO, "Creating design model inputs...");	

		ModuleADLWrapper moduleView = (ModuleADLWrapper)view;	
		ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)responsibilityStructure;
	
		// Initial design rule 0: Load a view from raw data and remove relations with orphans
		changed = moduleView.loadViewWithConsistencyChecking(coreResponsibilities);		
		
		// Initial design rule 1: Each leaf responsibility corresponds to a module 
		// (unless the responsibility has been already allocated in previous steps)
		// there may be cases of existing responsibilities that have been refined by tactics
		ArchEResponsibilityVO respVO = null;
		ArchEModuleVO moduleVO = null;
		ArchEVersionVO versionVO = (ArchEVersionVO)view.getParent().getCurrentVersion();
		
		for (Iterator<ArchEResponsibility> it = coreResponsibilities.getResponsibilities().iterator(); it.hasNext();) {		
			respVO = (ArchEResponsibilityVO)(it.next());
			
			// Create a module for each leaf responsibility who's not assigned to a module; 
			// this reasoning framework considers only leaf responsibilities.
			if(coreResponsibilities.isLeaf(respVO) 
					&& !moduleView.isAllocated(respVO)){
			
				moduleView.defineResponsibility(respVO);			
				// A new module is created				
				moduleVO = new ArchEModuleVO(versionVO);
				moduleVO.setName("(M) " + respVO.getName());					
				moduleVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
				boolean added = moduleView.defineModule(moduleVO);					
				moduleView.setResponsibilityAllocation(moduleVO, respVO, true);
				//printLog(2, Level.INFO, "Creating module ...  "+ moduleVO.getName()+" : "+added);	
				changed = true;
			}
		}
	
//		// Initial design rule 2: A dependency between two responsibilities maps to
//		// a dependency between corresponding modules			
		ArchEResponsibilityDependencyRelationVO respDependencyVO = null;
		List<ArchEModuleVO> parentList = null;
		List<ArchEModuleVO> childList = null;
		String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
		List<ArchERelation> dependencies = coreResponsibilities.getRelations(relationTypeVO);
		
		for (Iterator<ArchERelation> itDependencies = dependencies.iterator(); itDependencies.hasNext();) {
			
			respDependencyVO = (ArchEResponsibilityDependencyRelationVO)(itDependencies.next());
			
			// The modules each end of the dependency is assigned to
			parentList = moduleView.getModulesByResponsibility(respDependencyVO.getParent());
			childList = moduleView.getModulesByResponsibility(respDependencyVO.getChild());
			
			ArchEModuleVO mod1 = null;
			ArchEModuleVO mod2 = null;
			for (Iterator<ArchEModuleVO> i = parentList.iterator(); i.hasNext();) {
				mod1 = i.next();
				for (Iterator<ArchEModuleVO> j = childList.iterator(); j.hasNext();) {
					mod2 = j.next();
					moduleView.setModuleDependency(mod1, mod2, true);
					changed = true;
				}
			}
		}

		// Initial design rule 3: Delete the dependency between two modules that has no 
		// corresponding dependency between two responsibilities
		// This case is covered by method loadViewWithConsistencyChecking above

		return (changed);
	}

	private boolean initializeMVCCTASExampleView(ArchEView view, ArchEResponsibilityStructure responsibilityStructure, ArchERequirementModel requirementModel) throws ArchEException {
		if(view == null)
			throw new ArchEException("view must be not null");
		
		boolean changed = false;
		
		printLog(1, Level.INFO, "Creating design model inputs for QoSAExample-MVC example...");	

		ModuleADLWrapper moduleView = (ModuleADLWrapper)view;	
		ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)responsibilityStructure;
	
		// Initial design rule 0: Load a view from raw data and remove relations with orphans
		//changed = moduleView.loadViewWithConsistencyChecking(coreResponsibilities);		
		
		// Initial design rule 1: Each leaf responsibility corresponds to a module 
		// (unless the responsibility has been already allocated in previous steps)
		// there may be cases of existing responsibilities that have been refined by tactics
		ArchEResponsibilityVO respVO = null;
		ArchEVersionVO versionVO = (ArchEVersionVO)view.getParent().getCurrentVersion();
		
		boolean added = false;

		ArchEModuleVO viewVO = new ArchEModuleVO(versionVO);
		viewVO.setName("(M) View - A");				
		viewVO.setCostOfChange(2.0);
		//viewVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
		added = moduleView.defineModule(viewVO);					

		ArchEModuleVO modelVO = new ArchEModuleVO(versionVO);
		modelVO.setName("(M) Model - B");					
		modelVO.setCostOfChange(4.0);
		//modelVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
		added = moduleView.defineModule(modelVO);					

		ArchEModuleVO controllerVO = new ArchEModuleVO(versionVO);
		controllerVO.setName("(M) Controller - C");					
		controllerVO.setCostOfChange(5.0);
		//controllerVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
		added = moduleView.defineModule(controllerVO);			
		
		changed = true;

		// It creates all the responsibilities for MVC
//		ArchEResponsibilityVO resp1 = new ArchEResponsibilityVO(versionVO);
//		resp1.setName("R1");
//		coreResponsibilities.addResponsibility(resp1);
//		ArchEResponsibilityVO resp2 = new ArchEResponsibilityVO(versionVO);
//		resp1.setName("R2");
//		coreResponsibilities.addResponsibility(resp2);
//		ArchEResponsibilityVO resp3 = new ArchEResponsibilityVO(versionVO);
//		resp1.setName("R3");
//		coreResponsibilities.addResponsibility(resp3);
//		ArchEResponsibilityVO resp4 = new ArchEResponsibilityVO(versionVO);
//		resp1.setName("R4");
//		coreResponsibilities.addResponsibility(resp4);
		changed = true;

		for (Iterator<ArchEResponsibility> it = coreResponsibilities.getResponsibilities().iterator(); it.hasNext();) {		
			respVO = (ArchEResponsibilityVO)(it.next());
			added = moduleView.defineResponsibility(respVO);
			
//			if (respVO.getName().equals("Show Itinerary") || respVO.getName().equals("Attach to Model") )  {
//				added = moduleView.setResponsibilityAllocation(viewVO, respVO, true);
//				changed = true;				
			if (respVO.getName().equals("R1") )  {
					added = moduleView.setResponsibilityAllocation(viewVO, respVO, true);
					changed = true;				
			}
//			else if (respVO.getName().equals("Handle User Interactions") || respVO.getName().equals("Manage External Devices")) {
//				added = moduleView.setResponsibilityAllocation(controllerVO, respVO, true);
//				changed = true;					
//			}
			else if (respVO.getName().equals("R2")) {
				added = moduleView.setResponsibilityAllocation(controllerVO, respVO, true);
				changed = true;					
			}
			else {
				added = moduleView.setResponsibilityAllocation(modelVO, respVO, true);
				changed = true;				
				
			}

		}
	
//		// Initial design rule 2: A dependency between two responsibilities maps to
//		// a dependency between corresponding modules			
		ArchEResponsibilityDependencyRelationVO respDependencyVO = null;
		List<ArchEModuleVO> parentList = null;
		List<ArchEModuleVO> childList = null;
		String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
		List<ArchERelation> dependencies = coreResponsibilities.getRelations(relationTypeVO);
		
		for (Iterator<ArchERelation> itDependencies = dependencies.iterator(); itDependencies.hasNext();) {
			
			respDependencyVO = (ArchEResponsibilityDependencyRelationVO)(itDependencies.next());
			
			// The modules each end of the dependency is assigned to
			parentList = moduleView.getModulesByResponsibility(respDependencyVO.getParent());
			childList = moduleView.getModulesByResponsibility(respDependencyVO.getChild());
			
			ArchEModuleVO mod1 = null;
			ArchEModuleVO mod2 = null;
			for (Iterator<ArchEModuleVO> i = parentList.iterator(); i.hasNext();) {
				mod1 = i.next();
				for (Iterator<ArchEModuleVO> j = childList.iterator(); j.hasNext();) {
					mod2 = j.next();
					moduleView.setModuleDependency(mod1, mod2, true);
					changed = true;
				}
			}
		}

		// Initial design rule 3: Delete the dependency between two modules that has no 
		// corresponding dependency between two responsibilities
		// This case is covered by method loadViewWithConsistencyChecking above

		return (changed);
	}

	private boolean initializeArchETNExampleView(ArchEView view, ArchEResponsibilityStructure responsibilityStructure, ArchERequirementModel requirementModel) throws ArchEException {
		if(view == null)
			throw new ArchEException("view must be not null");
		
		boolean changed = false;
		
		printLog(1, Level.INFO, "Creating design model inputs for QoSAExample-MVC example...");	

		ModuleADLWrapper moduleView = (ModuleADLWrapper)view;	
		ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)responsibilityStructure;
	
		// Initial design rule 0: Load a view from raw data and remove relations with orphans
		//changed = moduleView.loadViewWithConsistencyChecking(coreResponsibilities);		
		
		// Initial design rule 1: Each leaf responsibility corresponds to a module 
		// (unless the responsibility has been already allocated in previous steps)
		// there may be cases of existing responsibilities that have been refined by tactics
		ArchEResponsibilityVO respVO = null;
		ArchEVersionVO versionVO = (ArchEVersionVO)view.getParent().getCurrentVersion();
		
		boolean added = false;

		ArchEModuleVO viewVO = new ArchEModuleVO(versionVO);
		viewVO.setName("(M) View - A");				
		viewVO.setCostOfChange(2.0);
		//viewVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
		added = moduleView.defineModule(viewVO);					

		ArchEModuleVO modelVO = new ArchEModuleVO(versionVO);
		modelVO.setName("(M) Model - B");					
		modelVO.setCostOfChange(4.0);
		//modelVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
		added = moduleView.defineModule(modelVO);					

		ArchEModuleVO controllerVO = new ArchEModuleVO(versionVO);
		controllerVO.setName("(M) Controller - C");					
		controllerVO.setCostOfChange(5.0);
		//controllerVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
		added = moduleView.defineModule(controllerVO);			
		
		changed = true;

		// It creates all the responsibilities for MVC
//		ArchEResponsibilityVO resp1 = new ArchEResponsibilityVO(versionVO);
//		resp1.setName("R1");
//		coreResponsibilities.addResponsibility(resp1);
//		ArchEResponsibilityVO resp2 = new ArchEResponsibilityVO(versionVO);
//		resp1.setName("R2");
//		coreResponsibilities.addResponsibility(resp2);
//		ArchEResponsibilityVO resp3 = new ArchEResponsibilityVO(versionVO);
//		resp1.setName("R3");
//		coreResponsibilities.addResponsibility(resp3);
//		ArchEResponsibilityVO resp4 = new ArchEResponsibilityVO(versionVO);
//		resp1.setName("R4");
//		coreResponsibilities.addResponsibility(resp4);
		changed = true;

		for (Iterator<ArchEResponsibility> it = coreResponsibilities.getResponsibilities().iterator(); it.hasNext();) {		
			respVO = (ArchEResponsibilityVO)(it.next());
			added = moduleView.defineResponsibility(respVO);
			
			if (respVO.getName().equals("Show Itinerary"))  {
				added = moduleView.setResponsibilityAllocation(viewVO, respVO, true);
				changed = true;				
			}
			else if (respVO.getName().equals("Create User Profile") || respVO.getName().equals("Manage Itinerary")) {
				added = moduleView.setResponsibilityAllocation(controllerVO, respVO, true);
				changed = true;					
			}
			else {
				added = moduleView.setResponsibilityAllocation(modelVO, respVO, true);
				changed = true;				
				
			}

		}
	
//		// Initial design rule 2: A dependency between two responsibilities maps to
//		// a dependency between corresponding modules			
		ArchEResponsibilityDependencyRelationVO respDependencyVO = null;
		List<ArchEModuleVO> parentList = null;
		List<ArchEModuleVO> childList = null;
		String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
		List<ArchERelation> dependencies = coreResponsibilities.getRelations(relationTypeVO);
		
		for (Iterator<ArchERelation> itDependencies = dependencies.iterator(); itDependencies.hasNext();) {
			
			respDependencyVO = (ArchEResponsibilityDependencyRelationVO)(itDependencies.next());
			
			// The modules each end of the dependency is assigned to
			parentList = moduleView.getModulesByResponsibility(respDependencyVO.getParent());
			childList = moduleView.getModulesByResponsibility(respDependencyVO.getChild());
			
			ArchEModuleVO mod1 = null;
			ArchEModuleVO mod2 = null;
			for (Iterator<ArchEModuleVO> i = parentList.iterator(); i.hasNext();) {
				mod1 = i.next();
				for (Iterator<ArchEModuleVO> j = childList.iterator(); j.hasNext();) {
					mod2 = j.next();
					moduleView.setModuleDependency(mod1, mod2, true);
					changed = true;
				}
			}
		}

		// Initial design rule 3: Delete the dependency between two modules that has no 
		// corresponding dependency between two responsibilities
		// This case is covered by method loadViewWithConsistencyChecking above

		return (changed);
	}

	//	private boolean initializeBizcoExampleView(ArchEView view, ArchEResponsibilityStructure responsibilityStructure, ArchERequirementModel requirementModel) throws ArchEException {
//		if(view == null)
//			throw new ArchEException("view must be not null");
//		
//		boolean changed = false;
//		
//		printLog(1, Level.INFO, "Creating design model inputs for Bizco-CS example...");	
//
//		ModuleADLWrapper moduleView = (ModuleADLWrapper)view;	
//		ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)responsibilityStructure;
//	
//		// Initial design rule 0: Load a view from raw data and remove relations with orphans
//		//changed = moduleView.loadViewWithConsistencyChecking(coreResponsibilities);		
//		
//		// Initial design rule 1: Each leaf responsibility corresponds to a module 
//		// (unless the responsibility has been already allocated in previous steps)
//		// there may be cases of existing responsibilities that have been refined by tactics
//		ArchEResponsibilityVO respVO = null;
//		ArchEVersionVO versionVO = (ArchEVersionVO)view.getParent().getCurrentVersion();
//		
//		boolean added = false;
//
//		ArchEModuleVO clientXVO = new ArchEModuleVO(versionVO);
//		clientXVO.setName("(M) Client - X");				
//		clientXVO.setCostOfChange(2.0);
//		//viewVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
//		added = moduleView.defineModule(clientXVO);					
//
//		ArchEModuleVO clientYVO = new ArchEModuleVO(versionVO);
//		clientYVO.setName("(M) Client - Y");					
//		clientYVO.setCostOfChange(4.0);
//		//modelVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
//		added = moduleView.defineModule(clientYVO);					
//
//		ArchEModuleVO serverVO = new ArchEModuleVO(versionVO);
//		serverVO.setName("(M) Server - ABC");					
//		serverVO.setCostOfChange(5.0);
//		//controllerVO.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
//		added = moduleView.defineModule(serverVO);			
//		
//		changed = true;
//
//		// It creates all the responsibilities for MVC
////		ArchEResponsibilityVO resp1 = new ArchEResponsibilityVO(versionVO);
////		resp1.setName("R1");
////		coreResponsibilities.addResponsibility(resp1);
////		ArchEResponsibilityVO resp2 = new ArchEResponsibilityVO(versionVO);
////		resp1.setName("R2");
////		coreResponsibilities.addResponsibility(resp2);
////		ArchEResponsibilityVO resp3 = new ArchEResponsibilityVO(versionVO);
////		resp1.setName("R3");
////		coreResponsibilities.addResponsibility(resp3);
////		ArchEResponsibilityVO resp4 = new ArchEResponsibilityVO(versionVO);
////		resp1.setName("R4");
////		coreResponsibilities.addResponsibility(resp4);
//		changed = true;
//
//		for (Iterator<ArchEResponsibility> it = coreResponsibilities.getResponsibilities().iterator(); it.hasNext();) {		
//			respVO = (ArchEResponsibilityVO)(it.next());
//			added = moduleView.defineResponsibility(respVO);
//			
//			if (respVO.getName().equals("Access Information X")) {
//				added = moduleView.setResponsibilityAllocation(clientXVO, respVO, true);
//				changed = true;				
//			}
//			else if (respVO.getName().equals("Access Information Y")) {
//				added = moduleView.setResponsibilityAllocation(clientYVO, respVO, true);
//				changed = true;				
//			}
//			else if (respVO.getName().equals("Find Server") || respVO.getName().equals("Send Request") )  {
//				added = moduleView.setResponsibilityAllocation(clientXVO, respVO, true);
//				added = moduleView.setResponsibilityAllocation(clientYVO, respVO, true);
//				changed = true;				
//			}
//			else {
//				added = moduleView.setResponsibilityAllocation(serverVO, respVO, true);
//				changed = true;				
//				
//			}
//
//		}
//	
////		// Initial design rule 2: A dependency between two responsibilities maps to
////		// a dependency between corresponding modules			
//		ArchEResponsibilityDependencyRelationVO respDependencyVO = null;
//		List<ArchEModuleVO> parentList = null;
//		List<ArchEModuleVO> childList = null;
//		String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
//		List<ArchERelation> dependencies = coreResponsibilities.getRelations(relationTypeVO);
//		
//		for (Iterator<ArchERelation> itDependencies = dependencies.iterator(); itDependencies.hasNext();) {
//			
//			respDependencyVO = (ArchEResponsibilityDependencyRelationVO)(itDependencies.next());
//			
//			// The modules each end of the dependency is assigned to
//			parentList = moduleView.getModulesByResponsibility(respDependencyVO.getParent());
//			childList = moduleView.getModulesByResponsibility(respDependencyVO.getChild());
//			
//			ArchEModuleVO mod1 = null;
//			ArchEModuleVO mod2 = null;
//			for (Iterator<ArchEModuleVO> i = parentList.iterator(); i.hasNext();) {
//				mod1 = i.next();
//				for (Iterator<ArchEModuleVO> j = childList.iterator(); j.hasNext();) {
//					mod2 = j.next();
//					moduleView.setModuleDependency(mod1, mod2, true);
//					changed = true;
//				}
//			}
//		}
//
//		// Initial design rule 3: Delete the dependency between two modules that has no 
//		// corresponding dependency between two responsibilities
//		// This case is covered by method loadViewWithConsistencyChecking above
//
//		return (changed);
//	}

	/**
	 * When executed, the suggested tactic leads to a transformation of
	 * the architecture
	 * 
	 * @param architecture the current architecture
	 * @param suggestedTactic the tactic to be applied 
	 * @throws ArchEException
	 */	
	@Override
	public boolean applySuggestedTactic(ArchEArchitecture architecture,
			ArchETryTacticResult suggestedTactic) throws ArchEException {
		
		printLog(3, Level.INFO, "About to apply (suggested) tactic ... on version= "+architecture.getCurrentVersion().getId());		

		if (suggestedTactic != null) { // The tactic configuration to apply the transformation 	
			
			// A command to execute the transformation is created
			if (suggestedTactic.getTacticName().equals(INSERT_INTERMEDIARY_MODULE_TACTIC)) {
				ArchEModuleVO targetModule = (ArchEModuleVO)(suggestedTactic.getParameters().get(0));
				Double costIntermediary = (Double)(suggestedTactic.getParameters().get(1));
				printLog(4, Level.INFO, "Target tactic --> " + suggestedTactic.getTacticName()+" to: "+targetModule.getName()+" cost: "+costIntermediary);
				
				ReduceCouplingModuleCommand transf1 = new ReduceCouplingModuleCommand(targetModule);				
				transf1.setCostForIntermediary(costIntermediary);
				transf1.setSourceArchitecture(architecture);
				transf1.execute();						
//				printLog(4, Level.INFO, "-->costOfTransformation: "+transf1.getSwitchingCost());
				printLog(4, Level.INFO, "-->costOfTransformation: "+transf1.getCostOfTransformation());
				return (true);
				
			}
			
			if (suggestedTactic.getTacticName().equals(SPLIT_RESPONSIBILITY_TACTIC)) {
				ArchEResponsibilityVO targetResp = (ArchEResponsibilityVO)(suggestedTactic.getParameters().get(0));
				printLog(4, Level.INFO, "Target tactic --> " + suggestedTactic.getTacticName()+" to: "+targetResp.getName());
				
				SplitResponsibilityCommand transf2 = new SplitResponsibilityCommand(targetResp);				
				transf2.setSourceArchitecture(architecture);
				transf2.execute();						
//				printLog(4, Level.INFO, "-->costOfTransformation: "+transf2.getSwitchingCost());
				printLog(4, Level.INFO, "-->costOfTransformation: "+transf2.getCostOfTransformation());
				return (true);				
			}

			if (suggestedTactic.getTacticName().equals(ADJUST_IMPACT_REFINED_RESPONSIBILITIES_TACTIC)) {
				ArchEResponsibilityVO parentResp = (ArchEResponsibilityVO)(suggestedTactic.getAt().get(0));
				ArchEScenarioVO parentSc = (ArchEScenarioVO)(suggestedTactic.getAt().get(3));
				ArchEResponsibilityVO leaf1Resp = (ArchEResponsibilityVO)(suggestedTactic.getAt().get(1));
				//ArchEResponsibilityVO leaf2Resp = (ArchEResponsibilityVO)(suggestedTactic.getAt().get(2));
				printLog(4, Level.INFO, "Target tactic --> " + suggestedTactic.getTacticName()+" to: "+parentResp.getName());
				
				AdjustImpactRefinedResponsibilitiesCommand transf3 = new AdjustImpactRefinedResponsibilitiesCommand(parentResp,parentSc);
				transf3.setLeafResponsibility(0, leaf1Resp); // Only try to delete one of the children responsibilities
				//transf3.setLeafResponsibility(1, leaf2Resp);
				transf3.setSourceArchitecture(architecture);
				transf3.execute();						
//				printLog(4, Level.INFO, "-->costOfTransformation: "+transf3.getSwitchingCost());
				printLog(4, Level.INFO, "-->costOfTransformation: "+transf3.getCostOfTransformation());
				return (true);				
			}

			if (suggestedTactic.getTacticName().equals(ABSTRACT_COMMON_RESPONSIBILITIES_TACTIC)) {
				ArchEResponsibilityVO parentRespA = (ArchEResponsibilityVO)(suggestedTactic.getAt().get(0));
				ArchEResponsibilityVO parentRespB = (ArchEResponsibilityVO)(suggestedTactic.getAt().get(1));
				printLog(4, Level.INFO, "Target tactic --> " + suggestedTactic.getTacticName()+" to: "+parentRespA.getName()+" and to: "+parentRespB.getName());
				
				AbstractCommonServicesCommand transf4 = new AbstractCommonServicesCommand(parentRespA,parentRespB);
				transf4.setSourceArchitecture(architecture);
				transf4.execute();						
//				printLog(4, Level.INFO, "-->costOfTransformation: "+transf4.getSwitchingCost());
				printLog(4, Level.INFO, "-->costOfTransformation: "+transf4.getCostOfTransformation());
				return (true);				
			}

		}
		
		return (false);
	}

	@Override
	public boolean applyTacticByUserQuestion(ArchEArchitecture architecture,
			ArchEUserQuestion userQuestion) throws ArchEException {

//		List answers = userQuestion.getAnswers();
//		System.out.println("ANSWERS RETURNED");
//		for(Iterator it = answers.iterator(); it.hasNext();)
//			System.out.println("--> "+it.next());

		if ((userQuestion != null) && (userQuestion.getAnswers().size() > 0)) {
			List userAnswers = userQuestion.getAnswers(); 			
			
			//	A command to execute the transformation is created
			if (userQuestion.getQuestionID().equals(INSERT_INTERMEDIARY_QUESTION)) {				
				if (userAnswers.get(0) != null) {
					// This is the default cost provided by the user for the intermediary
					ArchEModuleVO targetModule = (ArchEModuleVO)(userQuestion.getParameters().get(0));					
					Double costIntermediary = Double.parseDouble((String)(userAnswers.get(0)));
					printLog(4, Level.INFO, "Target tactic --> " + userQuestion.getQuestionID() + " to: "+targetModule.getName()+" cost: "+costIntermediary);
					
					ReduceCouplingModuleCommand transf1 = new ReduceCouplingModuleCommand(targetModule);
					transf1.setCostForIntermediary(costIntermediary);
					transf1.setSourceArchitecture(architecture);
					transf1.execute();	
					return (true);
				}
				else 
					return (false);				
			}			
			
			//	A command to execute the transformation is created
			if (userQuestion.getQuestionID().equals(SPLIT_RESPONSIBILITY_QUESTION)) {
				// The user question that was answered by the user
				if (userAnswers.get(0).equals("yes")) {
					ArchEResponsibilityVO targetResp = (ArchEResponsibilityVO)(userQuestion.getParameters().get(0));
					printLog(4, Level.INFO, "Target tactic --> " + userQuestion.getQuestionID()+" to: "+targetResp.getName());
					
					SplitResponsibilityCommand transf2 = new SplitResponsibilityCommand(targetResp);
					transf2.setSourceArchitecture(architecture);
					transf2.execute();						
					return (true);							
				}
				else
					return (false);
			}

			//	A command to execute the transformation is created
			if (userQuestion.getQuestionID().equals(ADJUST_REFINED_RESPONSIBILITIES_QUESTION)) {
				// The user question that was answered by the user
				ArchEResponsibilityVO parentResp = (ArchEResponsibilityVO)(userQuestion.getParameters().get(0));
				ArchEScenarioVO parentSc = (ArchEScenarioVO)(userQuestion.getParameters().get(3));
				
				AdjustImpactRefinedResponsibilitiesCommand transf3 = new AdjustImpactRefinedResponsibilitiesCommand(parentResp,parentSc);
				transf3.setSourceArchitecture(architecture);
				
				if (userAnswers.get(0).equals("1")) { // Option 1 (default): Keep the two leaves
					//printLog(4, Level.INFO, "Target tactic --> " + userQuestion.getQuestionID()+" to: "+parentResp.getName()+" OPTION1 (nothing executed) "+parentSc.getId());				
					return (true);							
				}
				else if (userAnswers.get(0).equals("2")) {
					ArchEResponsibilityVO leaf1 = (ArchEResponsibilityVO)(userQuestion.getParameters().get(1));
					//printLog(4, Level.INFO, "Target tactic --> " + userQuestion.getQuestionID()+" to: "+leaf1.getName()+" OPTION2 "+parentSc.getId());
					transf3.setLeafResponsibility(0, leaf1); // Keep the second leaf and remove the first one
					transf3.execute();						
					return (true);							
				}
				else if (userAnswers.get(0).equals("3")) {
					ArchEResponsibilityVO leaf2 = (ArchEResponsibilityVO)(userQuestion.getParameters().get(2));
					//printLog(4, Level.INFO, "Target tactic --> " + userQuestion.getQuestionID()+" to: "+leaf2.getName()+" OPTION3 "+parentSc.getId());
					transf3.setLeafResponsibility(1, leaf2); // Keep the first leaf and remove the second one
					transf3.execute();						
					return (true);							
				}
				else
					return (false);
			}

			//	A command to execute the transformation is created
			if (userQuestion.getQuestionID().equals(ABSTRACT_COMMON_RESPONSIBILITIES_QUESTION)) {
				// The user question that was answered by the user
				if (userAnswers.get(0).equals("yes")) {
					ArchEResponsibilityVO targetRespA = (ArchEResponsibilityVO)(userQuestion.getParameters().get(0));
					ArchEResponsibilityVO targetRespB = (ArchEResponsibilityVO)(userQuestion.getParameters().get(1));
					printLog(4, Level.INFO, "Target tactic --> " + userQuestion.getQuestionID()+" to: "+targetRespA.getName()+" and to: "+targetRespB.getName());
					
					AbstractCommonServicesCommand transf4 = new AbstractCommonServicesCommand(targetRespA, targetRespB);
					transf4.setSourceArchitecture(architecture);
					transf4.execute();						
					return (true);							
				}
				else
					return (false);
			}
		}

		return false;

	}
	
	@Override
	public ArchEUserQuestion describeTactic(ArchETryTacticResult tactic)
			throws ArchEException {

		ArchEUserQuestion userQuestion = null;
		ArchEObjectVO parent = null;
		printLog(3, Level.INFO, "About to describe tactic ... ");

		if (tactic != null) {
			printLog(4, Level.INFO, "Target tactic --> " + tactic.getTacticName());

			// A corresponding question is created
			if (tactic.getTacticName().equals(INSERT_INTERMEDIARY_MODULE_TACTIC)){				
				userQuestion = new ArchEUserQuestion();
				userQuestion.setQuestionID(INSERT_INTERMEDIARY_QUESTION);
				userQuestion.setAffectedFacts(tactic.getAt());				
				userQuestion.setParameters(tactic.getParameters());				
				parent = (ArchEObjectVO)(tactic.getAt().get(0));
				userQuestion.setParent(parent);				
				
				List optionList =  new ArrayList();
				userQuestion.setOptions(optionList);
				List defaultList =  new ArrayList();
				//defaultList.add(Double.toString(ChangeImpactAnalyzer.DEFAULT_MODULE_COST));
				double defaultCostIntermediary = (Double)(tactic.getParameters().get(1));
				defaultList.add(Double.toString(defaultCostIntermediary));
				userQuestion.setDefaults(defaultList);				
			}			

			// A corresponding question is created
			if (tactic.getTacticName().equals(SPLIT_RESPONSIBILITY_TACTIC)){
				userQuestion = new ArchEUserQuestion();
				userQuestion.setQuestionID(SPLIT_RESPONSIBILITY_QUESTION);
				userQuestion.setAffectedFacts(tactic.getAt());				
				userQuestion.setParameters(tactic.getParameters());								
				parent = (ArchEObjectVO)(tactic.getAt().get(0));
				userQuestion.setParent(parent);
				
				List defaultList =  new ArrayList();
				defaultList.add("yes");
				userQuestion.setDefaults(defaultList);				
				List optionList =  new ArrayList();
				userQuestion.setOptions(optionList);
			}

			// A corresponding question is created
			if (tactic.getTacticName().equals(ABSTRACT_COMMON_RESPONSIBILITIES_TACTIC)){
				userQuestion = new ArchEUserQuestion();
				userQuestion.setQuestionID(ABSTRACT_COMMON_RESPONSIBILITIES_QUESTION);
				userQuestion.setAffectedFacts(tactic.getAt());				
				userQuestion.setParameters(tactic.getParameters());								
				parent = (ArchEObjectVO)(tactic.getAt().get(0));
				userQuestion.setParent(parent);
				
				List defaultList =  new ArrayList();
				defaultList.add("yes");
				userQuestion.setDefaults(defaultList);				
				List optionList =  new ArrayList();
				userQuestion.setOptions(optionList);
			}

			// A corresponding question is created
			if (tactic.getTacticName().equals(ADJUST_IMPACT_REFINED_RESPONSIBILITIES_TACTIC)){
				userQuestion = new ArchEUserQuestion();
				userQuestion.setQuestionID(ADJUST_REFINED_RESPONSIBILITIES_QUESTION);
				userQuestion.setAffectedFacts(tactic.getAt());				
				//userQuestion.setParameters(tactic.getParameters());								
				userQuestion.setParameters(tactic.getAt());
				parent = (ArchEObjectVO)(tactic.getAt().get(0));
				userQuestion.setParent(parent);
				
				List defaultList =  new ArrayList();
				defaultList.add(1);
				userQuestion.setDefaults(defaultList);				
				List optionsList =  new ArrayList();
				optionsList.add(tactic.getAt().get(1));
				optionsList.add(tactic.getAt().get(2));
				userQuestion.setOptions(optionsList);
			}
		}		
		
		return (userQuestion);
	}

	/**
	 * Every time it's invoked, we check that the parameters of responsibilities
	 * and relationships are appropriately configured. We also check and remove
	 * any 'orphan' responsibility dependency.
	 * 
	 * @param requirementModel the current requirement model
	 * @param responsibilityStructure the current responsibility structure
	 * @throws ArchEException
	 */	
	@Override
	public boolean checkRFDependencies(ArchERequirementModel requirementModel,
			ArchEResponsibilityStructure responsibilityStructure)
			throws ArchEException {

		boolean changed = false;
		ArchECoreResponsibilityStructure coreStructure = ((ArchECoreResponsibilityStructure)responsibilityStructure);
		
		// Check for missing parameters in the responsibilities
		double costOfChange = ChangeImpactAnalyzer.DEFAULT_RESPONSIBILITY_COST;
		ArchEResponsibilityVO itemResp = null;
		for (Iterator<ArchEResponsibility> itResps = coreStructure.getResponsibilities().iterator(); itResps.hasNext();) {
			itemResp = (ArchEResponsibilityVO)(itResps.next());
			
			if (!itemResp.hasParameter(PARAMETER_COST_OF_CHANGE)) {
				// In case no costOfChange parameter exists, the responsibility is modified to include this parameter
				itemResp.defineParameter(PARAMETER_COST_OF_CHANGE, costOfChange);				
				changed = true;
			} 

			// The value costOfChange must be within the range [min .. max]
			double value = itemResp.getDoubleParameter(PARAMETER_COST_OF_CHANGE);
			if ((value > ChangeImpactAnalyzer.MAX_RESPONSIBILITY_COST) || (value < ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST)) {

				// Error reporting because of inconsistency
				String message = "Parameter "+PARAMETER_COST_OF_CHANGE+" must be in range ["
					+ ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST +" - "
					+ ChangeImpactAnalyzer.MAX_RESPONSIBILITY_COST + "] (value= "+ value + " !?)";
				ArchEAnalysisProblem problem = new ArchEAnalysisProblem(message, itemResp);
				this.setResponsibilityStructureStatus(RF_ERROR, RESPONSIBILITY_COST_OUT_OF_LIMITS_ERROR, problem);
				
				this.printLog(1, Level.INFO, message);
				//throw new ArchEException(message);
			}
			
		}
		
		// Check and delete orphan dependency relations among responsibilities
		String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
		ArchEResponsibilityDependencyRelationVO respDependencyVO = null;		

		for (Iterator<ArchERelation> itDependencies = coreStructure.getRelations(relationTypeVO).iterator(); itDependencies.hasNext();) {	
			respDependencyVO = (ArchEResponsibilityDependencyRelationVO)(itDependencies.next());			
			
			if ( respDependencyVO.getParent() == null
					|| respDependencyVO.getChild() == null
					|| !coreStructure.containResponsibility(respDependencyVO.getParent()) 
					|| !coreStructure.containResponsibility(respDependencyVO.getChild())) {
				// This is an orphan dependency that must be deleted from the responsibility structure
				coreStructure.deleteRelation(respDependencyVO);
				changed = true;
			}			
		}
		
		// Check for missing parameters in the relations
		double ripplingProbability = ChangeImpactAnalyzer.DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
		for (Iterator<ArchERelation> itDependencies = coreStructure.getRelations(relationTypeVO).iterator(); itDependencies.hasNext();) {			
			respDependencyVO = (ArchEResponsibilityDependencyRelationVO)(itDependencies.next());			
			
			if (!respDependencyVO.hasParameter(PARAMETER_PROBABILITY_INCOMING)) {
				// In case no probability parameter exists, the relation 
				// is modified to include this parameter
				respDependencyVO.defineParameter(PARAMETER_PROBABILITY_INCOMING, ripplingProbability);				
				changed = true;
			} 
			// The the value probabilityIncoming must be within the range [0..1]
			double value1 = respDependencyVO.getDoubleParameter(PARAMETER_PROBABILITY_INCOMING);
			if ((value1 > 1.0) || (value1 < 0)) {

				// Error reporting because of inconsistency
				String message = "Parameter "+PARAMETER_PROBABILITY_INCOMING+" must be in [0..1]";
				ArchEAnalysisProblem problem = new ArchEAnalysisProblem(message, respDependencyVO);
				this.setResponsibilityStructureStatus(RF_ERROR, WRONG_PROBABILITY_SETTING_ERROR, problem);
				
				this.printLog(1, Level.INFO, message);
				//throw new ArchEException(message);
			}
			
			if (!respDependencyVO.hasParameter(PARAMETER_PROBABILITY_OUTGOING)) {
				// In case no probability parameter exists, the relation 
				// is modified to include this parameter
				respDependencyVO.defineParameter(PARAMETER_PROBABILITY_OUTGOING, ripplingProbability);
				changed = true;
			} 
			// The value probabilityOutgoing must be within the range [0..1]
			double value2 = respDependencyVO.getDoubleParameter(PARAMETER_PROBABILITY_OUTGOING);
			if ((value2 > 1.0) || (value2 < 0)) {

				// Error reporting because of inconsistency
				String message = "Parameter "+PARAMETER_PROBABILITY_OUTGOING+" must be in [0..1]";
				ArchEAnalysisProblem problem = new ArchEAnalysisProblem(message, respDependencyVO);
				this.setResponsibilityStructureStatus(RF_ERROR, WRONG_PROBABILITY_SETTING_ERROR, problem);
				
				this.printLog(1, Level.INFO, message);
				//throw new ArchEException(message);
			}			
			
		} // End iteration over dependency relations
		
		return (changed);
		
	}

//	public boolean mergeResponsibilityRelationships(
//			ArchEResponsibilityStructure newResponsibilityStructure,
//			ArchEResponsibilityStructure parentResponsibilityStructure) {
//
//		boolean changed = false;
//		ArchECoreResponsibilityStructure newStructure = ((ArchECoreResponsibilityStructure)newResponsibilityStructure);
//		ArchECoreResponsibilityStructure previousStructure = ((ArchECoreResponsibilityStructure)newResponsibilityStructure);
//		
//		return (changed);
//	}

	@Override
	public List<ArchEUserQuestion> describeOtherThanTactic(
			ArchERequirementModel requirementModel,
			ArchEArchitecture architecture) throws ArchEException {

		List<ArchEUserQuestion> warningQuestions = new ArrayList<ArchEUserQuestion>();

		ArchEUserQuestion question = null;
		if (!this.isAnalysisValid()) {

			Integer key = null;
			ArchEAnalysisProblem problem = null;
			String text = null;

			for (Enumeration<Integer> enumErrors = reportedProblems.keys(); enumErrors.hasMoreElements();) {
				key = enumErrors.nextElement();
				problem = reportedProblems.get(key);
				text = problem.getMesssage()+" ( error= "+key+" )";

				question = new ArchEUserQuestion();
				question.setQuestionID(FIX_ANALYSIS_PARAMETERS_WARNING);
				question.setParent(problem.getSource());				
				question.setAffectedFacts(null);
				
				List parameters = new ArrayList();
				parameters.add(text);
				question.setParameters(parameters);	
				
				warningQuestions.add(question);
			}

			// This code is now called by ReasoningFrameworkExecutor after finishing the cycle
//			this.clearAnalysisStatus();
//			this.clearResponsibilityStructureStatus();
		}		
		else { 
			
			// Check if some splitResponsibility tactic was described in past interactions
			List<ArchEUserQuestion> splitRespQuestions = this.getAllUserQuestions(SPLIT_RESPONSIBILITY_QUESTION);
			// Warning: the questionID is not the same ID used by the executor to store the question
		
			ArchEUserQuestion split = null;
			if (splitRespQuestions.size() > 0) { // The tactic was described previously
				//System.out.println("Questions "+splitRespQuestions.size());
				ArchEResponsibilityVO target = null;
				for (Iterator<ArchEUserQuestion> it = splitRespQuestions.iterator(); it.hasNext();) {					
					split = it.next();
					target = (ArchEResponsibilityVO)(split.getAffectedFacts().get(0));					
					question = new ArchEUserQuestion();
					question.setQuestionID(DECIDE_ON_SPLITTING_WARNING);
					question.setParent(target);				
					question.setAffectedFacts(null);
					
					List parameters = new ArrayList();
					parameters.add(target);
					question.setParameters(parameters);
					
					warningQuestions.add(question);					
				}
				
			}

			// Check if some abstractCommonResponsibilities tactic was described in past interactions
			List<ArchEUserQuestion> abstractRespQuestions = this.getAllUserQuestions(ABSTRACT_COMMON_RESPONSIBILITIES_QUESTION);
			// Warning: the questionID is not the same ID used by the executor to store the question
		
			ArchEUserQuestion absCommon = null;
			if (abstractRespQuestions.size() > 0) { // The tactic was described previously
				//System.out.println("Questions "+splitRespQuestions.size());
				ArchEResponsibilityVO targetA = null;
				ArchEResponsibilityVO targetB = null;
				for (Iterator<ArchEUserQuestion> it = abstractRespQuestions.iterator(); it.hasNext();) {					
					absCommon = it.next();
					targetA = (ArchEResponsibilityVO)(absCommon.getAffectedFacts().get(0));					
					targetB = (ArchEResponsibilityVO)(absCommon.getAffectedFacts().get(1));					
					
					question = new ArchEUserQuestion();
					question.setQuestionID(DECIDE_ON_SPLITTING_WARNING);
					question.setParent(targetA);				
					question.setAffectedFacts(null);					
					List parametersA = new ArrayList();
					parametersA.add(targetA);
					question.setParameters(parametersA);					
					warningQuestions.add(question);					

					question = new ArchEUserQuestion();
					question.setQuestionID(DECIDE_ON_SPLITTING_WARNING);
					question.setParent(targetB);				
					question.setAffectedFacts(null);					
					List parametersB = new ArrayList();
					parametersB.add(targetB);
					question.setParameters(parametersB);					
					warningQuestions.add(question);					
}
				
			}

		}

		return (warningQuestions);
	}

	@Override
	public void beginLearning() throws ArchEException {
		// TODO Auto-generated method stub
		
	}

	@Override
	public List<ArchEUserQuestion> describeWhatLearned() throws ArchEException {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void learnBy(int typeOfLearning, Object[] args)
			throws ArchEException {
		// TODO Auto-generated method stub
		
	}
	
//	private static final double THRESHOLD_SPLITTING = 0.005; // For a responsibility cost normalized to range [0..1]
//	private static final double THRESHOLD_COUPLING = 0.33; // For a module coupling in range [0..1]
//	private static final double THRESHOLD_COMMON_SERVICES = 0.03; // For a responsibility cost normalized to range [0..1]
	
	/** 
	 * Here we define some 'screening' rules to configure the parameters of tactics
	 * 
	 * @param analyzer the change impact analysis just performed
	 * @param primaryReps the primary responsibilities in the analysis
	 * @param primaryModules the corresponding modules for the primary responsibilities
	 * @return
	 */
	protected List<ArchETryTacticResult> suggestTacticsBasedOnAnalysis(ChangeImpactAnalyzer analyzer,
			List<ArchEResponsibility> primaryResps,  ArchECoreResponsibilityStructure allResponsibilities, 
			ModuleADLWrapper moduleView, ArchEScenario currentScenario) {
		
		ArrayList<ArchETryTacticResult> modifTactics = new ArrayList<ArchETryTacticResult>();
		ArchETryTacticResult candidate = null;
		
		// Rule 1: Suggest a tactic to split a costly responsibility
		ModifiabilityTacticSolver solver1 = new TrySplitResponsibilitySolver(analyzer,primaryResps);
		solver1.setResponsibilityStructure(allResponsibilities);
		solver1.setModuleView(moduleView);
		ArchEResponsibilityVO targetResponsibility = null;
		if (solver1.searchForTactic(currentScenario)) {
			candidate = new ArchETryTacticResult();
			candidate.setTacticName(SPLIT_RESPONSIBILITY_TACTIC);
			candidate.setParameters(solver1.getParameters());
			targetResponsibility = (ArchEResponsibilityVO)(solver1.getTarget().get(0));
			candidate.setAt(solver1.estimateContext());
			candidate.setTacticDescription("Split Responsibility Tactic 1"+" ["+targetResponsibility.getName()+"]");
			printLog(3, Level.INFO, "Setting responsibility target 1 --> " + targetResponsibility.getName());
			modifTactics.add(candidate);			
		}
		
		// Rule 2: Suggest a tactic to insert an intermediary for a module
		ModifiabilityTacticSolver solver2 = new TryInsertIntermediaryModuleSolver(analyzer,primaryResps);
		solver2.setResponsibilityStructure(allResponsibilities);
		solver2.setModuleView(moduleView);
		ArchEModuleVO targetModule = null;
		if (solver2.searchForTactic(currentScenario)) {
			candidate = new ArchETryTacticResult();
			candidate.setTacticName(INSERT_INTERMEDIARY_MODULE_TACTIC);
			candidate.setParameters(solver2.getParameters());
			targetModule = (ArchEModuleVO)(solver2.getTarget().get(0));
			candidate.setAt(solver2.estimateContext());
			candidate.setTacticDescription("Insert Intermediary Tactic 1"+" ["+targetModule.getName()+"]");
			printLog(3, Level.INFO, "Setting module target 1 --> " + targetModule.getName());
			modifTactics.add(candidate);			
		}
	
		// Rule 3: Check the case in which an abstract responsibility is mapped to
		// two (or more) leaf responsibilities within the same scenario. If so, 
		// suggest a tactic to remove any of the mapped children from the scenario
		ModifiabilityTacticSolver solver3 = new TryAdjustImpactRefinedResponsibilitySolver(analyzer,primaryResps);
		solver3.setResponsibilityStructure(allResponsibilities);
		solver3.setModuleView(moduleView);
		ArchEResponsibilityVO abstractResponsibility = null;
		ArchEResponsibilityVO leaf1 = null;
		ArchEResponsibilityVO leaf2 = null;
		if (solver3.searchForTactic(currentScenario)) {
			candidate = new ArchETryTacticResult();
			candidate.setTacticName(ADJUST_IMPACT_REFINED_RESPONSIBILITIES_TACTIC);
			candidate.setParameters(solver3.getParameters());
			abstractResponsibility = (ArchEResponsibilityVO)(solver3.getTarget().get(0));
			leaf1 = (ArchEResponsibilityVO)(solver3.getTarget().get(1));
			leaf2 = (ArchEResponsibilityVO)(solver3.getTarget().get(2));
			candidate.setAt(solver3.estimateContext());
			candidate.setTacticDescription("Minimize Change Impact Tactic"+" ["+abstractResponsibility.getName()+"-"+leaf1.getName()+"-"+leaf2.getName()+"]");
			printLog(3, Level.INFO, "Setting parent responsibility --> " + abstractResponsibility.getName());
			printLog(3, Level.INFO, "Setting leaf1 responsibility --> " + leaf1.getName());
			printLog(3, Level.INFO, "Setting leaf2 responsibility --> " + leaf2.getName());
			printLog(3, Level.INFO, "Setting scenario --> " + ((ArchEScenarioVO)currentScenario).getId());
			modifTactics.add(candidate);			
		}

		// Rule 4: Suggest a tactic to abstract common services in a pair of costly responsibilities
		ModifiabilityTacticSolver solver4 = new TryAbstractCommonResponsibilitiesSolver(analyzer,primaryResps);
		solver4.setResponsibilityStructure(allResponsibilities);
		solver4.setModuleView(moduleView);
		ArchEResponsibilityVO targetResponsibilityA = null;
		ArchEResponsibilityVO targetResponsibilityB = null;
		if (solver4.searchForTactic(currentScenario)) {
			candidate = new ArchETryTacticResult();
			candidate.setTacticName(ABSTRACT_COMMON_RESPONSIBILITIES_TACTIC);
			candidate.setParameters(solver4.getParameters());
			targetResponsibilityA = (ArchEResponsibilityVO)(solver4.getTarget().get(0));
			targetResponsibilityB = (ArchEResponsibilityVO)(solver4.getTarget().get(1));
			candidate.setAt(solver4.estimateContext());
			candidate.setTacticDescription("Abstract Common Responsibilities Tactic 1"+" ["+targetResponsibilityA.getName()+" - "+targetResponsibilityB.getName()+" ]");
			printLog(3, Level.INFO, "Setting responsibility targetA 1 --> " + targetResponsibilityA.getName());
			printLog(3, Level.INFO, "Setting responsibility targetB 1 --> " + targetResponsibilityB.getName());
			modifTactics.add(candidate);			
		}
	
		return (modifTactics); // Here are the suggested tactics returned by this method
	}

	/**
	 * A command to execute a transformation that splits a particular responsibility
	 * into two children responsibilities, and then updates the module view accordingly
	 * Note: This transformation is assumed to leave the architecture in a consistent
	 * state (from the perspective of this reasoning framework)
	 */
	class SplitResponsibilityCommand implements RFArchitecturalTransformation {
	
		private ArchECoreArchitecture baseArchitecture = null;
		private ArchEResponsibility targetResponsibility = null; // Responsibility to be split
		private double costOfTransformation = 0.0;
		
		public double getCostOfTransformation() {
//		public double getSwitchingCost() {
			return (costOfTransformation);
		}
		
		public double getMaintenanceCost() {
			return (0.0);
		}
		
		public SplitResponsibilityCommand(ArchEResponsibility responsibility) {
			baseArchitecture = null;
			targetResponsibility = responsibility;
			costOfTransformation = 0.0;
		}
		
		/** 
		 * The transformation is accomplished in the following way: (see Modifiability Tactics TN)
		 *   1. The responsibility that was split is replaced by its two children
		 *   2. The responsibility being split is deleted from its module
		 *   3. Each of the new children is assigned to a new module (the old module is deleted
		 *   if  it not longer contains any other responsibility)
		 *   4. Any responsibility that is coupled (through a dependency relation) to the 
		 *   responsibility being split is now couple to the new responsibilities, with a strength
		 *   no greater than the original strength
		 *   5. The coupling between the new responsibilities must be specified
		 */
		public ArchEArchitecture execute() {
			
			costOfTransformation = 0.0;
			printLog(3, Level.INFO, "Executing transformation ... " + getClass().getName()+" on responsibility "+targetResponsibility);
			
			if (targetResponsibility != null) {				
							
				ModuleADLWrapper moduleView = (ModuleADLWrapper)(baseArchitecture.getView());
				ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)(baseArchitecture.getResponsibilityStructure());
				ArchEVersionVO versionVO = (ArchEVersionVO)moduleView.getParent().getCurrentVersion();
				
				// The new children responsibilities A and B are created and configured
				ArchEResponsibilityVO childrenA = new ArchEResponsibilityVO(versionVO); 
				childrenA.setName(targetResponsibility.getName()+"_child_"+ResponsibilityChildrenCounter);
				ResponsibilityChildrenCounter++;
				childrenA.setDescription("Child of "+targetResponsibility.getName()+" (due to splitting)");
				boolean added = moduleView.defineResponsibility(childrenA);
				added = coreResponsibilities.addResponsibility(childrenA);				
				printLog(4, Level.INFO,"Adding responsibility (in structure) ... "+childrenA.getName()+" : "+added);
				if (added)
					costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_CREATION;
				
				ArchEResponsibilityVO childrenB = new ArchEResponsibilityVO(versionVO); 
				childrenB.setName(targetResponsibility.getName()+"_child_"+ResponsibilityChildrenCounter);
				ResponsibilityChildrenCounter++;
				childrenB.setDescription("Child of "+targetResponsibility.getName()+" (due to splitting)");
				added = moduleView.defineResponsibility(childrenB);
				added = coreResponsibilities.addResponsibility(childrenB);
				printLog(4, Level.INFO,"Adding responsibility (in structure) ... "+childrenB.getName()+" : "+added);
				if (added)
					costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_CREATION;
				
				try {
					double costChildren = targetResponsibility.getDoubleParameter(PARAMETER_COST_OF_CHANGE);
					costChildren = costChildren * 0.3;
					if (costChildren < ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST)
						costChildren = ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST;
					childrenA.defineParameter(PARAMETER_COST_OF_CHANGE, costChildren);
					childrenB.defineParameter(PARAMETER_COST_OF_CHANGE, costChildren);
				} catch (ArchEException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			
				// It removes allocation relations from targetResponsibility to any old module in the view
				printLog(4, Level.INFO,"Removing allocations for targetResponsibility ______");
				List<ArchEModuleVO> oldModules = moduleView.getModulesByResponsibility(targetResponsibility);
				ArchEModuleVO mod = null;
				boolean removed;
				for (Iterator<ArchEModuleVO> itModules = oldModules.iterator(); itModules.hasNext();) {
					mod = itModules.next();
					removed = moduleView.setResponsibilityAllocation(mod, targetResponsibility, false);
					printLog(5, Level.INFO,"Removing allocation (from view) ... "+mod.getName()+"->"+targetResponsibility.getName()+" : "+removed);
					if (removed)
						costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_DEALLOCATION;
				}
				
				// It removes empty modules from the view
				List<ArchEModuleVO> existingModules = new ArrayList<ArchEModuleVO>(); 
				for (Iterator<ArchEModuleVO> itModules = oldModules.iterator(); itModules.hasNext();) {
					mod = itModules.next();
					if (moduleView.getCountAllocatedResponsibilities(mod) == 0) { 
						// There's no more responsibilities allocated to this module
						// It removes the module from the view (and it also updates
						// any module dependency and responsibility allocation in the matrices)
						removed = moduleView.removeModule(mod);
						printLog(4, Level.INFO,"Removing component (from view) ... "+mod.getName()+": "+removed);
						if (removed)
							costOfTransformation = costOfTransformation + COST_MODULE_REMOVAL;
					}
					else // Keep this list of modules 'without targetResponsibility' for later
						existingModules.add(mod); 
				}

				// The operation below removes the target responsibility from the view 
				// (and it also updates 'old' allocation relations for the target responsibility, if any)
				removed = moduleView.removeResponsibility(targetResponsibility);
				printLog(4, Level.INFO, "Removing responsibility (from view)... "+targetResponsibility.getName()+": "+removed);
				
				// A new module is created for children A				
				ArchEModuleVO moduleA = new ArchEModuleVO(versionVO);
				moduleA.setName("(M) " + childrenA.getName());					
				moduleA.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
				added = moduleView.defineModule(moduleA);
				printLog(4, Level.INFO,"Adding module (in view) ... "+moduleA.getName()+" : "+added);
				if (added)
					costOfTransformation = costOfTransformation + COST_MODULE_CREATION;

				// A new module is created for children B				
				ArchEModuleVO moduleB = new ArchEModuleVO(versionVO);
				moduleB.setName("(M) " + childrenB.getName());					
				moduleB.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
				added = moduleView.defineModule(moduleB);
				printLog(4, Level.INFO,"Adding module (in view) ... "+moduleB.getName()+" : "+added);
				if (added)
					costOfTransformation = costOfTransformation + COST_MODULE_CREATION;
				
				// The children responsibilities A and B are allocated to the corresponding modules
				added = moduleView.setResponsibilityAllocation(moduleB, childrenB, true);
				if (added)
					costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_ALLOCATION;
				added = moduleView.setResponsibilityAllocation(moduleA, childrenA, true);
				if (added)
					costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_ALLOCATION;			
				added = moduleView.setModuleDependency(moduleA, moduleB, true);
				printLog(4, Level.INFO,"Adding module dependency (in view) ... "+moduleA.getName()+"->"+moduleB.getName()+" : "+added);
				if (added)
					costOfTransformation = costOfTransformation + COST_MODULE_DEPENDENCY_ADDITION;

				// A dependency between the children responsibilities A and B is created
				ArchEResponsibilityDependencyRelationVO dependencyAB = new ArchEResponsibilityDependencyRelationVO(versionVO);
				dependencyAB.setParent(childrenA);
				dependencyAB.setChild(childrenB);
				double rippling = ChangeImpactAnalyzer.DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
				dependencyAB.defineParameter(PARAMETER_PROBABILITY_INCOMING, rippling * 0.45);
				dependencyAB.defineParameter(PARAMETER_PROBABILITY_OUTGOING, rippling * 0.45);
				added = coreResponsibilities.addRelation(dependencyAB);
				printLog(4, Level.INFO,"Adding dependency (in structure) ... "+childrenA.getName()+"->"+childrenB.getName()+" : "+added);

				// Any responsibility that was originally linked to targetResponsibility is now
				// redirected to the two added responsibilities A and B
				printLog(4, Level.INFO,"Updating dependencies for targetResponsibility (in structure)_____________");			
				ArchEResponsibilityVO respItem = null;
				ArchEResponsibilityDependencyRelationVO oldDependency = null;
				ArchEResponsibilityDependencyRelationVO newDependencyA = null;
				ArchEResponsibilityDependencyRelationVO newDependencyB = null;
				String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
				printLog(5, Level.INFO,"Dependencies (in structure) : "+coreResponsibilities.getRelations(relationTypeVO).size());
				for(Iterator<ArchEResponsibility> itResps = coreResponsibilities.getResponsibilities().iterator(); itResps.hasNext();) {
					respItem = (ArchEResponsibilityVO)(itResps.next());
					
					oldDependency = (ArchEResponsibilityDependencyRelationVO)(coreResponsibilities.getRelation(respItem, targetResponsibility, relationTypeVO));				
					if (oldDependency != null) { // This is an old dependency R --> targetResponsibility
						removed = coreResponsibilities.deleteRelation(oldDependency);
						printLog(5, Level.INFO,"Removing dependency (from structure) ... "+oldDependency.getParent().getName()+"->"+oldDependency.getChild().getName()+" : "+removed);
						
						// The rippling for the new dependencies is never greater than the original rippling
						double ripplingIncoming = rippling;
						double ripplingOutgoing = rippling;
						try {
							ripplingIncoming = oldDependency.getDoubleParameter(PARAMETER_PROBABILITY_INCOMING);
							ripplingOutgoing = oldDependency.getDoubleParameter(PARAMETER_PROBABILITY_OUTGOING);
						} catch (ArchEException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						
						newDependencyA = new ArchEResponsibilityDependencyRelationVO(versionVO);
						newDependencyA.setParent(respItem);
						newDependencyA.setChild(childrenA);
						newDependencyA.defineParameter(PARAMETER_PROBABILITY_INCOMING, ripplingIncoming * 0.5);
						newDependencyA.defineParameter(PARAMETER_PROBABILITY_OUTGOING, ripplingOutgoing * 0.5);
						added = coreResponsibilities.addRelation(newDependencyA);
						printLog(5, Level.INFO,"Adding dependency (in structure) ... "+newDependencyA.getParent().getName()+"->"+newDependencyA.getChild().getName()+" : "+added);
						
						newDependencyB = new ArchEResponsibilityDependencyRelationVO(versionVO);
						newDependencyB.setParent(respItem);
						newDependencyB.setChild(childrenB);
						newDependencyB.defineParameter(PARAMETER_PROBABILITY_INCOMING, ripplingIncoming * 0.5);
						newDependencyB.defineParameter(PARAMETER_PROBABILITY_OUTGOING, ripplingOutgoing * 0.5);
						added = coreResponsibilities.addRelation(newDependencyB);
						printLog(5, Level.INFO,"Adding dependency (in structure) ... "+newDependencyB.getParent().getName()+"->"+newDependencyB.getChild().getName()+" : "+added);
						
						// This updates the corresponding dependencies for those
						// modules containing the responsibility R
						oldModules = moduleView.getModulesByResponsibility(respItem);
						for (Iterator<ArchEModuleVO> itModules = oldModules.iterator(); itModules.hasNext();) {
							mod = itModules.next();

							added = moduleView.setModuleDependency(mod, moduleA, true);
							printLog(5, Level.INFO,"Adding module dependency (in view) ... "+mod.getName()+"->"+moduleA.getName()+" : "+added);
							added = moduleView.setModuleDependency(mod, moduleB, true);
							printLog(5, Level.INFO,"Adding module dependency (in view) ... "+mod.getName()+"->"+moduleB.getName()+" : "+added);
							if (added)
								costOfTransformation = costOfTransformation + COST_MODULE_DEPENDENCY_ADDITION;
							
							// If R is the only responsibility in the module, and R
							// has now been redirected to childrenA and childreB, then we need
							// to delete (set to false) the dependency between the module and those modules
							// that initially contained targetResponsibility (existingModules)
							if (moduleView.getCountAllocatedResponsibilities(mod) == 1) {
								ArchEModuleVO modTemp = null;
								for (Iterator<ArchEModuleVO> itExisting = existingModules.iterator(); itExisting.hasNext();) {
									modTemp = itExisting.next();
									removed = moduleView.setModuleDependency(mod, modTemp, false);
									printLog(5, Level.INFO,"Removing module dependency (from view) ... "+mod.getName()+"->"+modTemp.getName()+" : "+removed);
									if (removed)
										costOfTransformation = costOfTransformation + COST_MODULE_DEPENDENCY_DELETION;
								}
							}
						}
					} // End if for oldDependency
					
				}
					
				// We add refinement relations for childrenA and children B
				boolean refined = coreResponsibilities.refineResponsibility((ArchEResponsibilityVO)targetResponsibility, childrenA);
				printLog(4, Level.INFO,"Refining responsibility (in structure) ... "+targetResponsibility.getName()+" as "+childrenA.getName()+"  :"+refined);
				refined = coreResponsibilities.refineResponsibility((ArchEResponsibilityVO)targetResponsibility, childrenB);				
				printLog(4, Level.INFO,"Refining responsibility (in structure) ... "+targetResponsibility.getName()+" as "+childrenB.getName()+"  :"+refined);
	
			}
			
			return (baseArchitecture);
		}

		public void setSourceArchitecture(ArchEArchitecture architecture) {
			baseArchitecture = (ArchECoreArchitecture)architecture;
			
		}
	} // End SplitResponsibilityCommand

	/**
	 * A command to execute a transformation that inserts an intermediary between
	 * a module and the modules it's dependent on, and then updates the module view 
	 * accordingly.
	 * Note: This transformation is assumed to leave the architecture in a consistent 
	 * state (from the perspective of this reasoning framework)
	 */
	class ReduceCouplingModuleCommand implements RFArchitecturalTransformation {

			private ArchECoreArchitecture baseArchitecture = null;
			private ArchEModuleVO targetModule = null; // The module with strong coupling
			// that drives the need of an intermediary
			private double costChangeIntermediary;
			private double costOfTransformation = 0.0;
			
			public double getCostOfTransformation() {
//			public double getSwitchingCost() {
				return (costOfTransformation);
			}
			
			public double getMaintenanceCost() {
				return (0.0);
			}
			
			public ReduceCouplingModuleCommand(ArchEModuleVO module) {
				baseArchitecture = null;
				targetModule = module;
				costChangeIntermediary = ChangeImpactAnalyzer.DEFAULT_MODULE_COST;
				costOfTransformation = 0.0;
			}
			
			public void setCostForIntermediary(double cost) {
				costChangeIntermediary = cost;
			}
			
			/** 
			 * This transformation inserts an intermediary between the targetModule and the rest of the modules
			 * The transformation is accomplished in the following way: (see Modifiability Tactics TN)
			 *   1. Create a new responsibility to act as the intermediary, and create a new module for it
			 *   2. Delete the strength of coupling between the target module and the rest of the modules
			 *   3. Replace them with a strength of coupling between any linked module and the intermediary
			 *   module. Also add a strength of coupling between the target modules and the intermediary
			 *   if  it not longer contains any other responsibility)
			 *   4. Any responsibility that is coupled (through a dependency relation) to the 
			 *   responsibilities in target module is  now  coupled to the intermediary responsibility
			 *   5. The coupling between the new intermediary responsibility and the other responsibilities
			 *   must be specified
			 */
			public ArchEArchitecture execute() {

				costOfTransformation = 0.0;
				printLog(3, Level.INFO, "Executing transformation ... " + getClass().getName()+" on module "+targetModule);
				
				if (targetModule != null) {				

					ModuleADLWrapper moduleView = (ModuleADLWrapper)(baseArchitecture.getView());
					ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)(baseArchitecture.getResponsibilityStructure());
					ArchEVersionVO versionVO = (ArchEVersionVO)baseArchitecture.getCurrentVersion();
					
					List<ArchEModuleVO> oldModules = moduleView.getModules();

					// The new intermediary responsibility A is created and configured
					ArchEResponsibilityVO intermediaryA = new ArchEResponsibilityVO(versionVO);
					String nameIntermediaryResponsibility = targetModule.getName().substring(4);
					intermediaryA.setName(nameIntermediaryResponsibility+"_intermediary_"+ModuleIntermediaryCounter);
					intermediaryA.setDescription("Intermediary_responsibility_for "+targetModule.getName());
					boolean added = moduleView.defineResponsibility(intermediaryA);
					printLog(4, Level.INFO,"Creating responsibility (intermediary) ... "+intermediaryA.getName()+": "+added);
					added = coreResponsibilities.addResponsibility(intermediaryA);
					printLog(4, Level.INFO,"Creating responsibility (in structure) ... "+intermediaryA.getName()+": "+added);
					if (added)
						costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_CREATION;
					
					// The new intermediary module for A is created and configured
					ArchEModuleVO moduleA = new ArchEModuleVO(versionVO);
					moduleA.setName(targetModule.getName()+"_Intermediary_"+ModuleIntermediaryCounter);
					ModuleIntermediaryCounter++;
					moduleA.setCostOfChange(costChangeIntermediary);
//					if (costChangeIntermediary > ChangeImpactAnalyzer.MIN_MODULE_COST)
//						moduleA.setCostOfChange(costChangeIntermediary);
//					else	
//						moduleA.setCostOfChange(ChangeImpactAnalyzer.MIN_MODULE_COST);
					added = moduleView.defineModule(moduleA);
					printLog(4, Level.INFO,"Creating component (intermediary) ... "+moduleA.getName()+": "+added);
					if (added)
						costOfTransformation = costOfTransformation + COST_MODULE_CREATION;
					
					boolean updated = moduleView.setResponsibilityAllocation(moduleA, intermediaryA, true);					
					printLog(4, Level.INFO,"Allocating "+intermediaryA.getName()+" --> "+moduleA.getName()+" : "+updated);
					updated = moduleView.setModuleDependency(moduleA, targetModule, true);
					printLog(4, Level.INFO,"Setting module dependency "+moduleA.getName()+" --> "+targetModule.getName()+" : "+updated);				
					if (updated)
						costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_ALLOCATION;

					// Update the responsibility dependencies of the target module to the intermediary responsibility
					double rippling = ChangeImpactAnalyzer.DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
					List<ArchEResponsibility> targetModuleResps = moduleView.getResponsibilitiesByModule(targetModule);
					ArchEResponsibilityDependencyRelationVO respDependency = null;
					for (Iterator<ArchEResponsibility> itTargetResps = targetModuleResps.iterator(); itTargetResps.hasNext(); ) {
						respDependency = new ArchEResponsibilityDependencyRelationVO(versionVO);
						respDependency.setParent((ArchEResponsibilityVO)(itTargetResps.next()));
						respDependency.setChild(intermediaryA);
						respDependency.defineParameter(PARAMETER_PROBABILITY_INCOMING, rippling * 0.3);
						respDependency.defineParameter(PARAMETER_PROBABILITY_OUTGOING, rippling * 0.7);
						added = coreResponsibilities.addRelation(respDependency);
						printLog(4, Level.INFO,"New dependency (structure) "+intermediaryA.getName()+" --> "+respDependency.getParent().getName()+"rippling "+rippling+" : "+added);
					}

					
					// Update the dependencies of remaining modules with the new intermediary module
					targetModuleResps = moduleView.getResponsibilitiesByModule(targetModule);
					ArchEModuleVO mod = null;
					ArchEResponsibility targetResp = null;
					ArchEResponsibility modResp = null;
					ArchEResponsibilityDependencyRelationVO oldDependency = null;
					ArchEResponsibilityDependencyRelationVO newDependencyB = null;
					String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
					printLog(4, Level.INFO,"For each other module ...");
					for (Iterator<ArchEModuleVO> itModules = oldModules.iterator(); itModules.hasNext();) {
						mod = itModules.next();
						
						// Redirect existing module dependencies to the intermediary
						if (!mod.equals(targetModule) && !mod.equals(moduleA) && moduleView.hasDependency(mod, targetModule)) {
							// The two modules are equal if  they have the same name
							// (under the same version of the architecture)

							updated = moduleView.setModuleDependency(mod, targetModule, false);
							printLog(4, Level.INFO,"Removing module dependency "+mod.getName()+" --> "+targetModule.getName()+" : "+updated);
							if (updated)
								costOfTransformation = costOfTransformation + COST_MODULE_DEPENDENCY_DELETION;
							updated = moduleView.setModuleDependency(mod, moduleA, true);
							printLog(4, Level.INFO,"Setting module dependency "+mod.getName()+" --> "+moduleA.getName()+" : "+updated);
							if (updated)
								costOfTransformation = costOfTransformation + COST_MODULE_DEPENDENCY_ADDITION;
							
							// Redirect existing responsibility dependencies to go through 
							// the intermediary responsibility
							for (Iterator<ArchEResponsibility> itTargetResps = targetModuleResps.iterator(); 
								itTargetResps.hasNext();) {
								targetResp = itTargetResps.next();
								
								for (Iterator<ArchEResponsibility> itModResps = 
									moduleView.getResponsibilitiesByModule(mod).iterator(); itModResps.hasNext();) {
									
									modResp = itModResps.next();
									// The responsibility structure is updated with different dependency relations
									// TODO: There could be more than one responsibility dependency between a given pair of modules
									oldDependency = (ArchEResponsibilityDependencyRelationVO)(coreResponsibilities.getRelation(targetResp, modResp, relationTypeVO));
							
									if (oldDependency != null) {
										
										// The rippling for the new dependencies is never greater than the original rippling
										double ripplingIncoming = rippling;
										double ripplingOutgoing = rippling;
										try {
											ripplingIncoming = oldDependency.getDoubleParameter(PARAMETER_PROBABILITY_INCOMING);
											ripplingOutgoing = oldDependency.getDoubleParameter(PARAMETER_PROBABILITY_OUTGOING);
										} catch (ArchEException e) {
											// TODO Auto-generated catch block
											e.printStackTrace();
										}

										newDependencyB = new ArchEResponsibilityDependencyRelationVO(versionVO);
										newDependencyB.setParent(intermediaryA);
										newDependencyB.setChild((ArchEResponsibilityVO)modResp);
										newDependencyB.defineParameter(PARAMETER_PROBABILITY_INCOMING, ripplingIncoming * 0.75);
										newDependencyB.defineParameter(PARAMETER_PROBABILITY_OUTGOING, ripplingOutgoing * 0.75);
										added = coreResponsibilities.addRelation(newDependencyB);
										printLog(4, Level.INFO,"New dependency (structure) "+intermediaryA.getName()+" --> "+modResp.getName()+" : "+added);
										
										boolean deleted = coreResponsibilities.deleteRelation(oldDependency);
										printLog(4, Level.INFO,"Removing dependency (structure) "+oldDependency.getParent().getName()+" --> "+oldDependency.getChild().getName()+" : "+deleted);
									}									
								}								
							} // End of two 'for'
							
						}
					}
					
					printLog(3, Level.INFO, "Number of modules in the view --> "+moduleView.getModules().size());
					printLog(3, Level.INFO, "Number of module dependencies in the view --> "+moduleView.getCountModuleDependencies());
					printLog(3, Level.INFO, "Number of responsibility allocations in the view --> "+moduleView.getCountAllocatedResponsibilities());
					
				}			

				return (baseArchitecture);
			}

			public void setSourceArchitecture(ArchEArchitecture architecture) {
				baseArchitecture = (ArchECoreArchitecture)architecture;				
			}
	} // End ReduceCouplingModuleCommand
	
	/**
	 * A command to execute a transformation that deletes mapping from a scenario that contains
	 * both an abstract responsibility and two children responsibilities. This change only
	 * affects general responsibility structure, and therefore, the computation of the 'primary 
	 * responsibilities' for the scenario.
	 * Note: This transformation is assumed to leave the architecture in a consistent 
	 * state (from the perspective of this reasoning framework)
	 */
	class AdjustImpactRefinedResponsibilitiesCommand implements RFArchitecturalTransformation {

		private ArchECoreArchitecture baseArchitecture = null;
		private ArchEResponsibilityVO parentResponsibility = null; 
		private ArchEResponsibilityVO leaf1Responsibility = null; 
		private ArchEResponsibilityVO leaf2Responsibility = null; 
		private ArchEScenarioVO	parentScenario = null;
		private double costOfTransformation = 0.0;
		
		public double getCostOfTransformation() {
//		public double getSwitchingCost() {
			return (costOfTransformation);
		}
		
		public double getMaintenanceCost() {
			return (0.0);
		}
		
		public AdjustImpactRefinedResponsibilitiesCommand(ArchEResponsibilityVO parent, ArchEScenarioVO scenario) {
			parentResponsibility = parent;
			leaf1Responsibility = null;
			leaf1Responsibility = null;
			parentScenario = scenario;
			costOfTransformation = 0.0;
		}
		
		public void setLeafResponsibility(int index, ArchEResponsibilityVO resp) {
			if (index == 0)
				leaf1Responsibility = resp;
			if (index == 1)
				leaf2Responsibility = resp;
			return;
		}

		/** 
		 * This transformation removes one (or two) responsibilities mapped to a given scenario.
		 * The responsibility being removed is the result of a applying some previous tactic 
		 * (e.g., split a responsibility or abstract common responsibilities), in which a 
		 * responsibility refinement took place. Excluding a child responsibility (or leaf) not affected by
		 * the scenario can lead to more accurate change impact analysis for that scenario.
		 * The transformation is accomplished in the following way:
		 *   1. Find out which scenario-responsibility mapping (translation relationship) has to be removed
		 *   2. Remove the translation responsibility from the responsibility structure
		 */
		public ArchEArchitecture execute() {

			costOfTransformation = 0.0;
			if ((parentResponsibility != null) && (parentScenario != null)) {
				
				ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)(baseArchitecture.getResponsibilityStructure());
				
				List<ArchEResponsibility> children = coreResponsibilities.getChildrenResponsibilities(parentResponsibility);
				ArchEResponsibilityVO childResp = null;
				ArchETranslationRelationVO oldTranslation = null;
				boolean deleted = false;
				for (Iterator<ArchEResponsibility> it = children.iterator(); it.hasNext();) {
					childResp = (ArchEResponsibilityVO)(it.next());
					oldTranslation = null;
					
					// Delete only one of the leaf responsibilities
					if ((leaf1Responsibility != null) && (leaf1Responsibility.equals(childResp))) 
						oldTranslation = (ArchETranslationRelationVO)(coreResponsibilities.getRelation(parentScenario, leaf1Responsibility));

					if ((leaf2Responsibility != null) && (leaf2Responsibility.equals(childResp)))  
						oldTranslation = (ArchETranslationRelationVO)(coreResponsibilities.getRelation(parentScenario, leaf2Responsibility));


					if (oldTranslation != null) {
						deleted = coreResponsibilities.deleteRelation(oldTranslation);
						printLog(4, Level.INFO,"Removing translation (from structure) "+oldTranslation.getParent().getId()+" --> "+oldTranslation.getChild().getName()+" : "+deleted);																	
					}
					else 
						printLog(4, Level.INFO,"Removing translation (from structure) NULL");																	
				}
				
			}

			return (baseArchitecture);
		}

		public void setSourceArchitecture(ArchEArchitecture architecture) {
			baseArchitecture = (ArchECoreArchitecture)architecture;			
		}
		
	} // End AdjustImpactRefinedResponsibilitiesCommand
	
	/**
	 * A command to execute a transformation that splits two responsibilities that 
	 * share some functionality into two children responsibilities, and then moves
	 * the common portion to a new module (as a new responsibility)
	 * Note: This transformation is assumed to leave the architecture in a consistent 
	 * state (from the perspective of this reasoning framework)
	 */
	class AbstractCommonServicesCommand implements RFArchitecturalTransformation {
		
		private ArchECoreArchitecture baseArchitecture = null;
		private ArchEResponsibility targetResponsibilityA = null; // Responsibilities to be "shared"
		private ArchEResponsibility targetResponsibilityB = null; // Responsibilities to be "shared"
		private double costOfTransformation = 0.0;

		public AbstractCommonServicesCommand(ArchEResponsibilityVO respA, ArchEResponsibilityVO respB /*, ArchEScenarioVO scenario*/) {
			baseArchitecture = null;
			targetResponsibilityA = respA;
			targetResponsibilityB = respB;
			costOfTransformation = 0.0;			
		}
		
		public double getCostOfTransformation() {
//		public double getSwitchingCost() {
			return (costOfTransformation);
		}
		
		public double getMaintenanceCost() {
			return (0.0);
		}
	
		/** 
		 * The transformation is accomplished in the following way: (see Modifiability Tactics TN)
		 *   1. Identify the two responsibilities A y B that share some common functionality
		 *   2. Refine responsibility A into children A2 & C
		 *   3. Refine responsibility B into children B2 & C
		 *   4. Create a new module M and allocate responsibility C to that module
		 *   5. Define the responsibility dependencies A2-C and B2-C
		 *   6. Visit all the modules containing responsibility A and replace it by responsibility A2
		 *   7. Update all the dependencies to/from responsibility A so that they are now linked to A2
		 *   8. Repeat steps 5 & 6 with responsibilities B and B2
		 */
		public ArchEArchitecture execute() {
			
			// TODO: Many of the loops and operations below can be refactored in terms of helper methods
			// The refactoring would make the whole transformation more compact.
			
			costOfTransformation = 0.0;
			printLog(3, Level.INFO, "Executing transformation ... " + getClass().getName()+" on responsibilities "+targetResponsibilityA +" - "+targetResponsibilityB);
			
			if ((targetResponsibilityA != null) && (targetResponsibilityB != null)) {				
							
				ModuleADLWrapper moduleView = (ModuleADLWrapper)(baseArchitecture.getView());
				ArchECoreResponsibilityStructure coreResponsibilities = (ArchECoreResponsibilityStructure)(baseArchitecture.getResponsibilityStructure());
				ArchEVersionVO versionVO = (ArchEVersionVO)moduleView.getParent().getCurrentVersion();
				
//				String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
//				ArchERelation dependencyAB = coreResponsibilities.getRelation(targetResponsibilityA, targetResponsibilityB, relationTypeVO);

				// The new children (shared) responsibilities for responsibility A (A1 & A2) are created and configured
				ArchEResponsibilityVO childrenC = new ArchEResponsibilityVO(versionVO); 
				childrenC.setName(targetResponsibilityA.getName()+"_shared_"+ResponsibilityChildrenCounter);
				ResponsibilityChildrenCounter++;
				childrenC.setDescription("Child of "+targetResponsibilityA.getName()+" (due to abstracting common services)");
				boolean added = moduleView.defineResponsibility(childrenC);
				added = coreResponsibilities.addResponsibility(childrenC);				
				printLog(4, Level.INFO,"Adding responsibility (in structure) ... "+childrenC.getName()+" : "+added);
				if (added)
					costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_CREATION;
				
				ArchEResponsibilityVO childrenA2 = new ArchEResponsibilityVO(versionVO); 
				childrenA2.setName(targetResponsibilityA.getName()+"_child_"+ResponsibilityChildrenCounter);
				ResponsibilityChildrenCounter++;
				childrenA2.setDescription("Child of "+targetResponsibilityA.getName()+" (due to abstracting common services)");
				added = moduleView.defineResponsibility(childrenA2);
				added = coreResponsibilities.addResponsibility(childrenA2);				
				printLog(4, Level.INFO,"Adding responsibility (in structure) ... "+childrenA2.getName()+" : "+added);
				if (added)
					costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_CREATION;
				
				ArchEResponsibilityVO childrenB2 = new ArchEResponsibilityVO(versionVO); 
				childrenB2.setName(targetResponsibilityB.getName()+"_child_"+ResponsibilityChildrenCounter);
				ResponsibilityChildrenCounter++;
				childrenB2.setDescription("Child of "+targetResponsibilityB.getName()+" (due to sharing common services)");
				added = moduleView.defineResponsibility(childrenB2);
				added = coreResponsibilities.addResponsibility(childrenB2);
				printLog(4, Level.INFO,"Adding responsibility (in structure) ... "+childrenB2.getName()+" : "+added);
				if (added)
					costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_CREATION;

				try {
					double costChildrenAB = (targetResponsibilityA.getDoubleParameter(PARAMETER_COST_OF_CHANGE) 
							+ targetResponsibilityB.getDoubleParameter(PARAMETER_COST_OF_CHANGE)) / 2.0;
					costChildrenAB = costChildrenAB * 0.7;
					if (costChildrenAB < ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST)
						costChildrenAB = ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST;
					childrenC.defineParameter(PARAMETER_COST_OF_CHANGE, costChildrenAB);
					double costChildrenA = targetResponsibilityA.getDoubleParameter(PARAMETER_COST_OF_CHANGE);
					costChildrenA = costChildrenA * 0.3;
					if (costChildrenA < ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST)
						costChildrenA = ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST;
					childrenA2.defineParameter(PARAMETER_COST_OF_CHANGE, costChildrenA);

					double costChildrenB = targetResponsibilityB.getDoubleParameter(PARAMETER_COST_OF_CHANGE);
					costChildrenB = costChildrenB * 0.3;
					if (costChildrenB < ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST)
						costChildrenB = ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST;
					childrenB2.defineParameter(PARAMETER_COST_OF_CHANGE, costChildrenB);
				} catch (ArchEException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
	
				// It removes allocation relations from targetResponsibilityA to any old module in the view, 
				// changing the allocation to A2
				printLog(4, Level.INFO,"Removing allocations for targetResponsibilityA ______");
				List<ArchEModuleVO> oldModulesA = moduleView.getModulesByResponsibility(targetResponsibilityA);
				ArchEModuleVO modA = null;
				boolean removed;
				for (Iterator<ArchEModuleVO> itModules = oldModulesA.iterator(); itModules.hasNext();) {
					modA = itModules.next();
					removed = moduleView.setResponsibilityAllocation(modA, targetResponsibilityA, false);
					printLog(5, Level.INFO,"Removing allocation (from view) ... "+modA.getName()+"->"+targetResponsibilityA.getName()+" : "+removed);
					if (removed)
						costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_DEALLOCATION;
					moduleView.setResponsibilityAllocation(modA, childrenA2, true);
				}

				// It removes allocation relations from targetResponsibilityB to any old module in the view
				// changing the allocation to B2
				printLog(4, Level.INFO,"Removing allocations for targetResponsibilityB ______");
				List<ArchEModuleVO> oldModulesB = moduleView.getModulesByResponsibility(targetResponsibilityB);
				ArchEModuleVO modB = null;
				for (Iterator<ArchEModuleVO> itModules = oldModulesB.iterator(); itModules.hasNext();) {
					modB = itModules.next();
					removed = moduleView.setResponsibilityAllocation(modB, targetResponsibilityB, false);
					printLog(5, Level.INFO,"Removing allocation (from view) ... "+modB.getName()+"->"+targetResponsibilityB.getName()+" : "+removed);
					if (removed)
						costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_DEALLOCATION;
					moduleView.setResponsibilityAllocation(modB, childrenB2, true);
				}

				// The operation below removes the target responsibilities A & B from the view 
				// (and it also updates 'old' allocation relations for the target responsibility, if any)
				removed = moduleView.removeResponsibility(targetResponsibilityA);
				printLog(4, Level.INFO, "Removing responsibility (from view)... "+targetResponsibilityA.getName()+": "+removed);
				removed = moduleView.removeResponsibility(targetResponsibilityB);
				printLog(4, Level.INFO, "Removing responsibility (from view)... "+targetResponsibilityB.getName()+": "+removed);
				
				// A new module is created for children A1 + B1				
				ArchEModuleVO moduleC = new ArchEModuleVO(versionVO);
				moduleC.setName("(M) " + targetResponsibilityA.getName()+"|"+targetResponsibilityB.getName()+"_shared"+ModuleIntermediaryCounter);
				ModuleIntermediaryCounter++;
				moduleC.setCostOfChange(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
				added = moduleView.defineModule(moduleC);
				printLog(4, Level.INFO,"Adding module (in view) ... "+moduleC.getName()+" : "+added);
				if (added)
					costOfTransformation = costOfTransformation + COST_MODULE_CREATION;

				// The children responsibilities A1 and B1 are allocated to the same module
				added = moduleView.setResponsibilityAllocation(moduleC, childrenC, true);
				if (added)
					costOfTransformation = costOfTransformation + COST_RESPONSIBILITY_ALLOCATION;
				
				// A dependency between the children responsibilities A1 and A2 is created
				ArchEResponsibilityDependencyRelationVO dependencyA1C = new ArchEResponsibilityDependencyRelationVO(versionVO);
				dependencyA1C.setParent(childrenC);
				dependencyA1C.setChild(childrenA2);
				double rippling = ChangeImpactAnalyzer.DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
				dependencyA1C.defineParameter(PARAMETER_PROBABILITY_INCOMING, rippling * 0.45);
				dependencyA1C.defineParameter(PARAMETER_PROBABILITY_OUTGOING, rippling * 0.45);
				added = coreResponsibilities.addRelation(dependencyA1C);
				printLog(4, Level.INFO,"Adding dependency (in structure) ... "+childrenC.getName()+"->"+childrenA2.getName()+" : "+added);

				// A dependency between the children responsibilities B1 and B2 is created
				ArchEResponsibilityDependencyRelationVO dependencyB1C = new ArchEResponsibilityDependencyRelationVO(versionVO);
				dependencyB1C.setParent(childrenC);
				dependencyB1C.setChild(childrenB2);
				dependencyB1C.defineParameter(PARAMETER_PROBABILITY_INCOMING, rippling * 0.45);
				dependencyB1C.defineParameter(PARAMETER_PROBABILITY_OUTGOING, rippling * 0.45);
				added = coreResponsibilities.addRelation(dependencyB1C);
				printLog(4, Level.INFO,"Adding dependency (in structure) ... "+childrenC.getName()+"->"+childrenB2.getName()+" : "+added);
				
				// Any responsibility that was originally linked to targetResponsibilityA  is now
				// redirected to responsibilities A2
				printLog(4, Level.INFO,"Updating dependencies for targetResponsibilityA (in structure)_____________");			
				ArchEResponsibilityVO respItem = null;
				ArchEResponsibilityDependencyRelationVO oldDependency = null;
				ArchEResponsibilityDependencyRelationVO newDependencyA2 = null;
				String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
				printLog(5, Level.INFO,"Dependencies (in structure) : "+coreResponsibilities.getRelations(relationTypeVO).size());
				for(Iterator<ArchEResponsibility> itResps = coreResponsibilities.getResponsibilities().iterator(); itResps.hasNext();) {
					respItem = (ArchEResponsibilityVO)(itResps.next());
					
					oldDependency = (ArchEResponsibilityDependencyRelationVO)(coreResponsibilities.getRelation(respItem, targetResponsibilityA, relationTypeVO));				
					if (oldDependency != null) { // This is an old dependency R --> targetResponsibilityA
						removed = coreResponsibilities.deleteRelation(oldDependency);
						printLog(5, Level.INFO,"Removing dependency (from structure) ... "+oldDependency.getParent().getName()+"->"+oldDependency.getChild().getName()+" : "+removed);
						
						// The rippling for the new dependencies is never greater than the original rippling
						double ripplingIncoming = rippling;
						double ripplingOutgoing = rippling;
						try {
							ripplingIncoming = oldDependency.getDoubleParameter(PARAMETER_PROBABILITY_INCOMING);
							ripplingOutgoing = oldDependency.getDoubleParameter(PARAMETER_PROBABILITY_OUTGOING);
						} catch (ArchEException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						
						newDependencyA2 = new ArchEResponsibilityDependencyRelationVO(versionVO);
						newDependencyA2.setParent(respItem);
						newDependencyA2.setChild(childrenA2);
						newDependencyA2.defineParameter(PARAMETER_PROBABILITY_INCOMING, ripplingIncoming * 0.45);
						newDependencyA2.defineParameter(PARAMETER_PROBABILITY_OUTGOING, ripplingOutgoing * 0.45);
						added = coreResponsibilities.addRelation(newDependencyA2);
						printLog(5, Level.INFO,"Adding dependency (in structure) ... "+newDependencyA2.getParent().getName()+"->"+newDependencyA2.getChild().getName()+" : "+added);	
						
					} // End if for oldDependency					
				}

				// Any responsibility that was originally linked to targetResponsibilityB  is now
				// redirected to responsibilities B2 (A2)
				printLog(4, Level.INFO,"Updating dependencies for targetResponsibilityB (in structure)_____________");			
				respItem = null;
				oldDependency = null;
				ArchEResponsibilityDependencyRelationVO newDependencyB2 = null;
				relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
				printLog(5, Level.INFO,"Dependencies (in structure) : "+coreResponsibilities.getRelations(relationTypeVO).size());
				for(Iterator<ArchEResponsibility> itResps = coreResponsibilities.getResponsibilities().iterator(); itResps.hasNext();) {
					respItem = (ArchEResponsibilityVO)(itResps.next());
					
					oldDependency = (ArchEResponsibilityDependencyRelationVO)(coreResponsibilities.getRelation(respItem, targetResponsibilityB, relationTypeVO));				
					if (oldDependency != null) { // This is an old dependency R --> targetResponsibilityA
						removed = coreResponsibilities.deleteRelation(oldDependency);
						printLog(5, Level.INFO,"Removing dependency (from structure) ... "+oldDependency.getParent().getName()+"->"+oldDependency.getChild().getName()+" : "+removed);
						
						// The rippling for the new dependencies is never greater than the original rippling
						double ripplingIncoming = rippling;
						double ripplingOutgoing = rippling;
						try {
							ripplingIncoming = oldDependency.getDoubleParameter(PARAMETER_PROBABILITY_INCOMING);
							ripplingOutgoing = oldDependency.getDoubleParameter(PARAMETER_PROBABILITY_OUTGOING);
						} catch (ArchEException e) {
							// TODO Auto-generated catch block
							e.printStackTrace();
						}
						
						newDependencyB2 = new ArchEResponsibilityDependencyRelationVO(versionVO);
						newDependencyB2.setParent(respItem);
						newDependencyB2.setChild(childrenB2);
						newDependencyB2.defineParameter(PARAMETER_PROBABILITY_INCOMING, ripplingIncoming * 0.45);
						newDependencyB2.defineParameter(PARAMETER_PROBABILITY_OUTGOING, ripplingOutgoing * 0.45);
						added = coreResponsibilities.addRelation(newDependencyB2);
						printLog(5, Level.INFO,"Adding dependency (in structure) ... "+newDependencyB2.getParent().getName()+"->"+newDependencyB2.getChild().getName()+" : "+added);	
						
					} // End if for oldDependency					
				}

				// We add refinement relations for childrenA1  and childrenA2
				boolean refined = coreResponsibilities.refineResponsibility((ArchEResponsibilityVO)targetResponsibilityA, childrenC);
				printLog(4, Level.INFO,"Refining responsibility (in structure) ... "+targetResponsibilityA.getName()+" as "+childrenC.getName()+"  :"+refined);
				refined = coreResponsibilities.refineResponsibility((ArchEResponsibilityVO)targetResponsibilityA, childrenA2);				
				printLog(4, Level.INFO,"Refining responsibility (in structure) ... "+targetResponsibilityA.getName()+" as "+childrenA2.getName()+"  :"+refined);		

				// We add refinement relations for childrenB1  and childrenB2
				refined = coreResponsibilities.refineResponsibility((ArchEResponsibilityVO)targetResponsibilityB, childrenC);
				printLog(4, Level.INFO,"Refining responsibility (in structure) ... "+targetResponsibilityB.getName()+" as "+childrenC.getName()+"  :"+refined);
				refined = coreResponsibilities.refineResponsibility((ArchEResponsibilityVO)targetResponsibilityB, childrenB2);				
				printLog(4, Level.INFO,"Refining responsibility (in structure) ... "+targetResponsibilityB.getName()+" as "+childrenB2.getName()+"  :"+refined);
				
				// If the scenario is automatically mapped to the children responsibilities A1, B1 & C, 
				// then tactic "Adjust Impact of Refined Responsibilities" should work as usual

			}
			
			return (baseArchitecture);
		}

		public void setSourceArchitecture(ArchEArchitecture architecture) {
			baseArchitecture = (ArchECoreArchitecture)architecture;
			
		}
		
	} // End AbstractCommonServicesCommand
	
}
